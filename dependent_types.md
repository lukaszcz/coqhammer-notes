# Proper handling of dependent types in the CoqHammer translation

*Design notes for TODO.md point 9 — written 2026-07-05, based on an investigation of
`src/plugin/coq_transl.ml` (branch `dependent-types`), the JAR 2018 CoqHammer paper,
the TYPES 2016 shallow-embedding paper, and the extraction / hammer literature.
Companion document: `notes/extraction.md` (TODO points 7 and 9) — a detailed digest
of Letouzey's thesis, the per-constructor match-axiom proposal, and the
extraction-as-translation-architecture view. This file incorporates its conclusions;
where the two overlap, they agree, and §5.1 adopts its well-founded-recursion
caveat as a hard constraint. Siblings: `notes/monomorphisation.md` (TODO 5/6),
`notes/type_guards.md` (TODO 2/3). All FOL outputs below verified with
`Hammer_transl` on this branch.*

## TL;DR

1. **Root cause of TODO 9**: `case_lifting` (`src/plugin/coq_transl.ml:453`) returns
   an opaque `$_generic_case` constant, with no axiom, for any match on a
   `Prop`-sorted scrutinee — killing the definitional equation — and the typing
   axiom is unusable because subset types reach the guard generator as opaque
   `HasType(w, sig(A,P))` atoms.
2. **The design is extraction + specification extraction, all shallow**: erase terms
   following Letouzey's `E` (singleton propositional matches → their unique branch;
   `exist(A,P,v) ↦ v`; `proj1_sig ↦` identity; proof arguments already dropped), and
   complete the guard generator into a realizability translation that expands subset
   types into formulas **inline, per occurrence** — `guard(w, {x:A | P x}) :=
   guard(w,A) ∧ P w` — never as `HasType` atoms plus unfolding axioms, and never as
   bridge equations left for the ATP to rewrite with (deep embeddings; rejected).
3. **On the TODO's example** this yields literally the two requested axioms:
   `$_def_h : ∀x y z. h(x,y,z) = z` and
   `∀x y z. x=y ∧ y=z → x = h(x,y,z)` (plus `nat` guards), with `sig`/`exist`/
   `proj1_sig` absent from the output.
4. **Hard constraint** (from `notes/extraction.md`): unfolding equations for
   `Acc`-style well-founded recursion must keep the erased `Prop` preconditions as
   implication premises — the unconditional form is inconsistent in FOL
   (`div a O = S (div a O)` vs `n_Sn`). Extraction is protected by weak evaluation;
   an equational axiomatization is not.
5. One instance-classification analysis (`Empty`/`PropSingleton`/`Subset`/`Enum`)
   drives all cases, including `prod`/`sum`/`sigT`/`sumbool` with propositional
   arguments (per-instance, dissolving the JAR paper's "four variants of `prod`"
   problem). Synergistic with TODO 7's per-constructor match equations; phased
   implementation plan in §7, evaluation plan in §8.

---

## 1. The problem

TODO point 9 asks for proper handling of:

1. functions that use dependent types in a non-trivial way,
2. case analysis on small propositional inductive types (`and`, `eq`, `False`, `Acc`, ...)
   in *informative* (non-`Prop`) positions,
3. `sig`, `sigT`, `sig2`, and `prod`/`sum`/`sigT` instantiated with propositional
   arguments,

and for **specification extraction**: in addition to a *definition* of the erased
function, an axiom derived from its (dependent) *type*.

### Ground truth (reproduced on this branch, Rocq 9.1)

For the TODO's running example

```coq
Definition h (x y z : nat) (p : x = y /\ y = z) : {u : nat | x = u} :=
  match p with
  | conj p1 p2 => exist (fun u => x = u) z (eq_trans p1 p2)
  end.
```

`Hammer_transl "h"` currently produces exactly three axioms and **no definitional
equation** (`$_def_h` is absent):

```
$_lam_15:    ∀v0 v1. $_lam_15(v0,v1) <=> v0 = v1              (the lifted predicate λu. x = u)
$_type_12:   ∀w. HasType(w,$_type_12) <=>
               ∀x. nat(x) → ∀y. nat(y) → ∀z. nat(z) →
                 (x=y ∧ y=z → HasType(w x y z, sig(nat, $_lam_15(x))))
$_typeof_h:  HasType(h, $_type_12)
```

Two observations that shape the whole design:

- The *guard* `$_type_12` **already contains the desired specification implication**
  `x=y ∧ y=z → HasType(h x y z, sig nat (λu. x=u))`. The only reason it is unusable is
  that `HasType(w, sig(A,P))` is an opaque atom: nothing connects it to `P`.
  The generic inversion axiom for `sig`
  (`$_inversion_sig : HasType(X, sig(A,P)) → ∃x. HasType(x,A) ∧ P x ∧ X = exist(A,P,x)`)
  does connect it, but only through an existential and the `exist` constructor, and it
  is only in scope when `sig` itself is among the selected premises.
- The definitional equation is lost in exactly one place: `case_lifting`
  (`src/plugin/coq_transl.ml:411`) returns an opaque fresh constant
  `$_generic_case_N` whenever the type of the matched term is `Prop`-sorted
  (`coq_transl.ml:453`), emitting **no axiom at all**; and `lambda_lifting`
  (`coq_transl.ml:335-350`) delegates a `Case`-bodied definition wholesale to
  `case_lifting`, so the `$_def_h` axiom is never produced.

Two more data points from live experiments:

- `eq_rect`-based transport is opaque: for
  `Definition tr P a b (e : a = b) (x : P a) : P b := eq_rect a P x b e.`
  we get `$_def_tr : tr(P,a,b,x) = eq_rect(nat,a,P,x,b)` and `eq_rect` itself has no
  usable definition (its body is a match on a proof of `eq`). Every function using
  dependent rewriting, `Program`, `Function`, or well-founded recursion
  (`Fix_F` matches on an `Acc` proof) is therefore computationally opaque to the ATPs.
- `proj1_sig` *does* get a usable definitional axiom (its match is on `sig`, which is
  `Set`-sorted, so the normal branch of `case_lifting` runs), but it goes through an
  existential + `exist`, i.e. three axiom applications for what should be an identity.

---

## 2. Where the current translation stands (code map)

Pipeline: `hammer_main.ml` exports kernel terms as `hhterm`s →
`coq_convert.ml:to_coqdef` builds the `coqterm` IR (proof bodies and opaque
constants become `Const(name)`, i.e. typing-axiom-only) → `coq_transl.ml`
translates, with `Coq_typing.check_prop` (NbE, `coq_typing.ml:177,250`) as the sort
oracle. The relevant mechanisms:

- **Proof erasure** is already pervasive and correct at the *term* level:
  `Prop`-typed binders are substituted by `Cast($Proof, ty)`
  (`coqterms.ml:460 subst_proof`), proof variables convert to `$Proof`
  (`coq_transl.ml:607-611`), and **applications to `$Proof` arguments are dropped**
  (`coq_transl.ml:580-583`). So `exist (fun u => x=u) z (eq_trans p1 p2)` already
  converts to `exist(nat-pred-stuff, z)` — proof argument gone.
- **Dependent products** are handled correctly on the formula/guard side:
  `prop_to_formula` (`coq_transl.ml:643`) and `type_to_guard` (`coq_transl.ml:675`)
  thread the context so `∀x. T(x,α) → …` guards mention `x` freely; propositional
  domains become implications with the proof variable erased.
- **Value extraction for non-`Prop` matches already exists and is good**: the non-Prop
  branch of `case_lifting` (`coq_transl.ml:456-526`) emits
  `∀…. (∃args. matched = Cᵢ(args) ∧ f(…) = branchᵢ) ∨ …` via `mk_inversion`
  (`coq_transl.ml:203`) and handles nested matches recursively (`hlp`,
  `coq_transl.ml:467-521`).
- **Inversion axioms already carry propositional constructor arguments as formulas**:
  `$_inversion_sig` contains the conjunct `P x`. `mk_inversion_conjs`
  (`coq_transl.ml:168-176`) skips `Prop` args in the generated *equalities* but the
  guard machinery inserts their *formulas*.
- What a definition gets is decided in `add_def_axioms` (`coq_transl.ml:1065`) and
  `add_def_eq_axiom` (`coq_transl.ml:888`); the "unusable typing axiom" comes from
  `add_typing_axiom` (`coq_transl.ml:834`) → `make_guard` (`coq_transl.ml:659`), whose
  base case is an opaque `HasType(x, convert ty)`.

**The gaps are therefore narrow and well-localized:**

| # | Gap | Location |
|---|-----|----------|
| G1 | Matches on proofs with informative result → opaque constant, no axiom | `coq_transl.ml:453` |
| G2 | `HasType(w, I(p̄))` is opaque for propositional-content types (`sig` etc.); the spec in the typing guard is unreachable | `make_guard` / `type_to_guard` base cases |
| G3 | No collapse of singleton informative content (`sig A P ≅ A`); everything goes through `exist`/∃ indirection | translation-wide |
| G4 | `prod`/`sum`/`sigT` instantiated with `Prop` arguments handled by the generic (Type-sorted) scheme only | per-occurrence sort analysis missing |
| G5 | (adjacent) primitive projections `$Proj` unsupported → `unsupported__N` constants | `coq_convert.ml:175-177` |

---

## 3. Literature

**CoqHammer itself.**
Czajka & Kaliszyk, *Hammer for Coq: Automation for Dependent Type Theory*, J. Autom.
Reasoning 61 (2018). Section 5 defines the `F`/`G`/`C` translation implemented in
`coq_transl.ml`; Section 9 ("Limitations") states precisely the point-9 problems:
matches on small propositional inductive types "are translated to a fresh constant
about which nothing is assumed", proposition detection for sort-ambiguous type formers
(`prod` fed propositions) "is relatively simplistic", and it explicitly points to
Letouzey's extraction thesis, suggesting the translation "be factorized reusing the
intermediate representation from [60]". The translation *globally assumes proof
irrelevance* (proofs collapse to `prf`/`$Proof`) — this is the license for everything
proposed below.

**The sound core.**
Czajka, *A Shallow Embedding of Pure Type Systems into First-Order Logic*, TYPES 2016
(LIPIcs 97). Proves soundness of the core translation for *proof-irrelevant* PTSs
(piPTSs): proof terms are collapsed by an ε-reduction (`x^{*p} →ε ε`, `ε M →ε ε`,
`λx:A.ε →ε ε`) built into conversion. Inductive types are out of scope there — the
extensions below should be viewed as extending the piPTS erasure to inductive
constructions, following extraction.

**Extraction (the model for the term side).**
Letouzey, *Programmation fonctionnelle certifiée: l'extraction de programmes dans
l'assistant Coq*, PhD thesis, Université Paris-Sud, 2004 (HAL tel-00150912; an
English translation exists on his page); *A New Extraction for Coq*, TYPES 2002;
*Extraction in Coq: an Overview*, CiE 2008. See `notes/extraction.md` §3 for a
section-by-section digest of the thesis. Extraction's `E` function erases exactly
the content we mishandle:
(i) logical parts (Prop-sorted) become `□`; (ii) **singleton/empty propositional
elimination** — a match on a proof, allowed by CIC's elimination restriction only for
empty or singleton propositional inductives — is erased to its unique branch (or dead
code); (iii) **the singleton optimization**: an informative inductive with one
constructor carrying exactly one informative argument (`sig`) is identified with that
argument's type; `exist a p ↦ a`, `proj1_sig ↦ id`; (iv) `prod`/`sum` with
propositional components lose those components. TODO 9's "program extraction" half is
literally Letouzey's `E`. Three details verified against the TYPES 2002 paper matter
for the design: (a) the singleton criterion is "one constructor whose arguments are
all logical, parameters put aside" and the elimination rule is
`Cases e of f end → (f □ … □)`, applicable even under lambdas — this is §5.1's E1
rule verbatim; (b) the `cast : nat = bool → nat → bool` example shows singleton
elimination of `eq` can produce "type-incorrect" terms — harmless in untyped FOL but
the source of the reconstruction caveat in §6; (c) restriction (iii) ("the guard
argument of a fixpoint can be logical while the fixpoint is informative", i.e.
`Acc`-style recursion) is handled by extraction only through *weak* evaluation —
closures never unfold — a protection that an equational FOL axiomatization does not
have; §5.1 makes the consequences a hard constraint. What extraction does *not*
need — and what we must add — is the "specification extraction" half; the thesis
itself supplies its blueprint: the simulation predicates `⟦τ⟧₂` / `Î` of §2.4
(worked out for Euclidean division with a `sig` result type in §2.4.4), of which
CoqHammer's current guards and inversion axioms are the Prop-content-free shadow
(`notes/extraction.md` §5.2).

**Realizability (the model for the type side).**
Paulin-Mohring, *Extracting Fω's programs from proofs in the Calculus of
Constructions*, POPL 1989. The specification axiom for a function `c = t : τ` is
exactly the realizability statement "`E(t)` realizes `τ`", and the realizability
predicate `R(w, τ)` is defined *structurally on τ*:
`R(w, Πx:α.β) = ∀x. R(x,α) → R(w x, β)`;
`R(w, {x:A | P x}) = R(w,A) ∧ P w`; etc.
CoqHammer's guard function `G` (`make_guard`/`type_to_guard`) *is* a degenerate
realizability translation that stops at atoms. The principled fix for G2 is to
complete `G` into `R`. Extraction correctness (Letouzey ch. 2, after Paulin-Mohring)
is then the soundness argument: for every definition, the erased term realizes its
type in the proof-irrelevant model, so the emitted spec axiom is true in that model.

**CIC meta-theory.** The elimination restriction (Prop → Type elimination only for
*empty* and *singleton* propositional inductives — all constructor arguments
propositional, at most one constructor: `False`, `True`, `eq`, `and`, `Acc`, ...) is
what makes the case-erasure rule *total*: any kernel-accepted informative match on a
proof is empty or singleton, so "translate the unique branch" is never a choice among
branches. (Caveats: `-impredicative-set`, and `SProp`'s separate rules; see §7.)
Gilbert, Cockx, Sozeau, Tabareau, *Definitional Proof-Irrelevance without K*, POPL
2019, is the reference for `SProp` and for why proof-irrelevant erasure of `eq`
matches does not license K in general — relevant to the soundness discussion in §6.

**Other hammers / translations.**
- Sledgehammer's HOL→FOL chain (Meng & Paulson, *Translating higher-order clauses to
  first-order clauses*, JAR 2008; Blanchette, Böhme, Popescu, Smallbone, *Encoding
  monomorphic and polymorphic types*, LMCS 2016): λ-lifting, arity optimization, and
  sound type-guard/tag encodings justified by monotonicity. CoqHammer already uses the
  Meng–Paulson optimizations; the monotonicity work is the reference point for TODO 3/6
  (omitting guards), orthogonal to point 9 but worth citing because the same
  guard-omission questions reappear for the new spec axioms.
- **Lean-auto** (Qian, Wu et al., *Lean-auto: An Interface between Lean 4 and Automated
  Theorem Provers*, CAV 2025, arXiv:2505.14929): translates dependent type theory into
  monomorphic HOL via a λC preprocessing stage + monomorphization. Notably it does
  *not* attempt genuine dependent types: dependently typed constants are handled by
  instantiation (monomorphization) and by using Lean's **equational lemmas** — the
  elaborator-generated `f.eq_n : f args = rhs` facts — instead of raw `match`
  compilations. This is important precedent: the *equational specification* of a
  dependently-typed function, not its kernel term, is the right currency for ATPs.
  Our design generates such equations inside the translation (Rocq does not provide
  them for plain `Definition`s; the Equations plugin does, but only for its own
  definitions).
- **When Agda met Vampire** (Šinkarovs & Rawson, arXiv:2602.18844, 2026): restricts to
  an equational-Horn fragment shared by Agda and Vampire, with two-way translation.
  Confirms the same lesson from the opposite direction: what survives translation
  usefully is equations + Horn specifications, which is exactly what
  program + specification extraction produces.
- MizAR's soft type system (Urban; Wiedijk, *Mizar's Soft Type System*, TPHOLs 2007):
  types-as-predicates ("soft typing") is the same design point as CoqHammer's
  `HasType` guards; subset types there are handled by *adjective* predicates attached
  to the term — structurally identical to the `R(w, sig A P) = R(w,A) ∧ P w` rule.
- Tammet & Smith, *Optimized encodings of fragments of type theory in first-order
  logic*, J. Log. Comput. 1998 — early precedent for encoding dependent products with
  type predicates in untyped FOL.
- Sozeau & Mangin, *Equations reloaded* (ICFP 2019): elaborates dependent pattern
  matching into eliminators and derives equations + graph + functional elimination.
  An alternative *source* of specifications when available, but not a general solution
  (stdlib and most user code don't use Equations).

---

## 4. Design principles

1. **Translation = program extraction + specification extraction.** The FOL image of
   an informative constant `c = t : τ` should be (a) equations describing Letouzey's
   `E(t)` and (b) the realizability formula `R(c, τ)`. Everything below instantiates
   this slogan.
2. **One semantic model.** Every generated axiom must hold in the *proof-irrelevant
   erasure model*: interpret each closed informative term by its extraction `E(t)`,
   each proposition by its truth in Coq + proof irrelevance, and `HasType(w, τ)` by
   "w realizes τ". This is the same model the existing translation implicitly targets
   (it already collapses proofs to `$Proof` and translates `eq` to `=`), so the
   extensions do not add a *new* soundness debt category — they extend the existing
   one uniformly. The known unsound corners (functional extensionality, universe
   constraints, guard omission — JAR paper §5.6) remain and are unchanged.
3. **Reuse the existing machinery.** The non-Prop branch of `case_lifting`, the
   guard/inversion generators, and the proof-argument dropping in `convert` already do
   80% of the work. No parallel pipeline, no new IR.
4. **Shallowness is a hard requirement, not an optimization.** The efficiency of the
   whole translation rests on propositions becoming FOL *formulas computed at
   translation time* (the stated design rationale of the TYPES 2016 paper: "it is
   important for efficiency … that the embedding be shallow"), and TODO 5 makes the
   same point for instantiation: do it at the translation level so the output can be
   further optimised — never leave unfolding work to the ATP. Concretely for this
   design: subset/propositional content of types must be expanded into formulas
   *per occurrence*; erased constructors and projections must be simplified away
   *per occurrence*. Axiom-mediated encodings — a `HasType(w, sig(A,P))` atom plus
   an unfolding axiom the ATP has to instantiate, or bridge equations like
   `exist(A,P,x) = x` that the ATP has to rewrite with — are deep embeddings of
   exactly the kind the TODO's example rules out, and are acceptable only as
   fallbacks in positions where no shallow form exists (see §5.2/§5.3). `HasType`
   leaf atoms remain only where they already are the soft-typing base case
   (atomic/opaque types: `nat(x)`, `list(nat, x)` after TODO 6).
5. **Everything behind options,** consistent with `coq_transl_opts.ml`, so the eval
   harness (`eval/`) can ablate each piece.

---

## 5. The design

### 5.0 New analysis: propositional-content classification of inductive instances

Add a function (new module `coq_erasure.ml`, or in `coq_typing.ml`) classifying an
inductive *instance* — inductive name `I` plus actual parameters `p̄`, in context —
by inspecting the constructor types instantiated at `p̄`, using the existing
`check_prop` oracle on each constructor argument type:

- `Empty` — no constructors (`False`).
- `PropSingleton` — `I p̄` is `Prop`-sorted, one constructor, all arguments
  propositional (this is exactly CIC's singleton-elimination criterion): `True`,
  `and`, `eq`, `Acc`, `JMeq`, ...
- `Subset(carrier, specs)` — `I p̄` is `Set`/`Type`-sorted, one constructor with
  **exactly one informative argument** of type `carrier` and propositional arguments
  with (instantiated) types `specs` (functions of the informative argument):
  `sig A P` → `Subset(A, [P x])`; `sig2 A P Q` → `Subset(A, [P x; Q x])`;
  *per instance*: `prod A B` with `B` a proposition → `Subset(A, [B])`;
  `sigT A (fun _ => P)` with `P : Prop` likewise. Two side conditions:
  (i) `carrier` must not mention `I` itself (Letouzey's condition on informative
  singleton unboxing, thesis §4.3 — a recursive carrier makes the collapse
  ill-founded); (ii) require at least one *dropped propositional* argument, i.e. do
  not collapse purely informative single-field wrappers (`Inductive t := C : nat → t`)
  — collapsing those is not needed for TODO 9, is not what motivates the erasure
  model, and identifying `C x` with `x` gratuitously merges types the ATP could
  otherwise keep apart. Such wrappers stay `Regular`.
- `Enum(specs per constructor)` — every constructor has only propositional arguments
  (per instance): `sumbool A B` (`{A}+{B}`), `prod A B` with both args propositional,
  `exception`-style types. Values are bare constructor constants with attached specs.
- `Regular` — everything else (`sum A B` with one propositional side falls here:
  two constructors, one informative argument on one side; it is handled by the
  ordinary constructor/inversion machinery plus per-instance argument dropping,
  which the existing `convert` already performs).

Classification is cheap (constructor types are in `Defhash`), memoizable keyed on
`(I, propositionality mask of p̄)`, and must treat `SProp` like `Prop` (§7).

### 5.1 E1 — Erase informative matches on proofs (fixes G1)

In `case_lifting` (`coq_transl.ml:453`), replace the unconditional
`generic_match ()` for Prop-sorted matched types by:

- **`Empty`**: keep the current behaviour (fresh opaque constant, no axiom). This is
  dead code under a `False` hypothesis; nothing useful can or need be said. (Optional
  refinement: emit nothing at all and translate the whole surrounding branch away —
  not worth the complexity initially.)
- **`PropSingleton`**: let the single branch be `λx₁:τ₁…λxₖ:τₖ. s`. Translate the
  case expression as `C(s[Cast($Proof,τᵢ)/xᵢ])` — i.e. peel the branch lambdas,
  substitute the proof sentinel for each bound variable (they are all proofs, by the
  singleton criterion; `subst_proof` at `coqterms.ml:460` does exactly this), and
  continue with the ordinary equation-emitting path so that the `axname`
  (`$_def_h` when reached from a definition) **is** emitted, exactly like the `_`
  branch of `lambda_lifting` (`coq_transl.ml:352-370`). Nested matches recurse
  naturally since the result is converted by `convert`.
- Anything else (multi-constructor `Prop` matched informatively — only possible with
  `-impredicative-set` or exotic kernels): keep `generic_match ()` as a safe fallback.

Consequences, all verified against the current code paths:

- `h`: body becomes `exist (λu. x=u) z (eq_trans …)`; `convert` drops the proof
  argument; with E3 below the `exist` collapses; we get
  **`$_def_h : ∀x y z. h(x,y,z) = z`** (modulo optional closure guards), the first
  half of TODO 9's request.
- `eq_rect`/`eq_rec`/`eq_ind` (and their `_r` variants) become identities:
  `eq_rect(A,a,P,x,b) = x`. All transport disappears. This is extraction's behaviour
  and is the single biggest practical win for "functions using dependent types
  non-trivially" (vectors, `Fin`, dependent records, `Program` obligations).
- `Fix_F`/`Acc_rect` (well-founded recursion): `Acc` is `PropSingleton`
  (its constructor argument is a proof), so the same erasure applies and
  `Function`/`Program Fixpoint`/`Fix` definitions — currently completely opaque —
  become equationally visible to the ATPs. **But with a hard constraint**
  (discovered in `notes/extraction.md`, TL;DR 4 and §5.1, and traceable to
  restriction (iii) of Letouzey's TYPES 2002 paper): the *unconditional* unfolding
  equation of a function defined by recursion on an erased proof is in general
  **not a Coq theorem and can be inconsistent** in FOL. Example: erasing wf-division
  unconditionally yields the instance `div a O = S (div a O)`, which contradicts the
  perfectly legitimate premise `∀n. n ≠ S n` (`n_Sn` in the stdlib). Extraction gets
  away with the erasure because target-language evaluation is weak (the diverging
  closure is never forced); an equational axiomatization is "already applied" and
  has no such protection. Therefore: when the erased match/fix recurses through the
  proof (the `Acc`/`Fix_F` pattern — detectable as a `fix` whose structurally
  decreasing argument is propositional), the emitted definitional equations **must
  keep the erased `Prop` hypotheses of the enclosing definition as implication
  premises** (`∀a b. b ≠ O → div a b = …`), i.e. force the `opt_lambda_guards`-style
  treatment for that definition's proof binders. This is mandatory for consistency,
  not an option. A staged fallback for phase 1: keep `Acc`-guarded fixpoints on
  `generic_match` initially and enable the conditional-equation form as a separate,
  separately-evaluated step.
- Impossible branches in indexed matches (`vector`-style `match … with end` via
  `False_rect` or an `eq` discrimination) hit the `Empty` rule and stay harmless
  opaque constants inside branches that the inversion axiom already renders
  unreachable.

**Guard policy** (refined by the analysis above and in `notes/extraction.md` §2.3):

- *Non-recursive `PropSingleton` erasure* (`and`, `True`, and `eq` when the branch
  makes no recursive call through the proof): unconditional equation by default,
  mirroring extraction. For `eq` specifically, a more cautious variant guards the
  equation with `F(τ_p)` (the equation between the lifted variables); add
  `opt_erasure_guards` (default `false`) choosing the guarded form, analogous to
  `opt_closure_guards`; §6 discusses the trade-off.
- *Recursion through the erased proof* (`Acc`-style): erased `Prop` preconditions
  are **mandatory** implication premises, per the previous bullet. Not an option.

Note the standing TODO at `coq_transl.ml:750-752` (proof variables missing from
`cctx` in case lifting) is subsumed by this policy for the erased cases.

### 5.2 S — Complete the guard function into a realizability translation (fixes G2)

The guard computation (`make_guard`, `coq_transl.ml:659`; `type_to_guard`,
`coq_transl.ml:675`) is already a *shallow* transformer: it turns a type into a FOL
formula at translation time, per occurrence, recursing through `Π`. The fix is to
keep recursing where it currently stops: a subset-type leaf must be expanded into a
formula **inline, at each occurrence**, never emitted as a `HasType(w, sig(…))` atom
(there is no axiom the ATP could be expected to unfold it with — and giving it one
would be a deep embedding, reintroducing at the spec level exactly the indirection
this whole exercise removes). Extend the base case: when the (NbE-normalized, via
`Coq_typing.eval`) guard type is an instance `I p̄` classified as:

- **`Subset(carrier, specs)`**:
  `guard(w, I p̄)  :=  guard(w, carrier) ∧ ⋀ᵢ prop_to_formula(specᵢ[w])`,
  where `specᵢ[w]` is the propositional argument's type with the informative
  constructor variable replaced by the guarded term `w` and β-simplified (`simpl`,
  `coqterms.ml:462`) **before** conversion — so for `h` we get `x = w` directly
  instead of a detour through a lifted `$_lam` predicate.
- **`Enum(specs)`** (values are bare erased constructors, so a type atom is
  meaningful): expand the guard inline into the disjunction of per-constructor
  cases with their spec formulas —
  `guard(w, sumbool(A,B)) := (w = left ∧ F(A)) ∨ (w = right ∧ F(B))` — rather than
  leaving a bare `HasType` atom that must be joined with a separately-selected
  inversion axiom. (The per-type `$_inversion_*` axiom stays, for occurrences that
  arise without a guard context, but the guard itself is self-contained.)
- otherwise: current behaviour.

Because `add_typing_axiom` funnels through `make_guard`/`type_to_guard`, this makes
every typing axiom of a constant whose type involves subset types into a usable,
directly-stated specification axiom — **with one adjustment**: `opt_type_lifting`
must be suppressed for types with erasable content. Today `h`'s typing axiom is
split into `HasType(h, $_type_12)` plus a reified-type unfolding axiom — one more
indirection than necessary even now, and it would bury the spec two instantiation
hops deep. When the classification finds erasable content anywhere in a constant's
type, emit the specification axiom in the *applied, fully unfolded* form (the
`type_to_guard` ∀-form over the constant applied to fresh variables), exactly as
TODO 9's example displays it. For `h` this yields directly:

```
∀x y z. nat(x) → nat(y) → nat(z) →
  (x=y ∧ y=z  →  nat(h(x,y,z)) ∧ x = h(x,y,z))
```

— precisely TODO 9's requested specification axiom, obtained not as a special case
but as the general realizability reading of `h`'s type. In Letouzey's terms this
guard extension is the simulation predicate `Î` for `sig` after singleton unboxing
(thesis §2.4 + §4.3; the div example in §2.4.4 collapses to exactly this
pre/post-condition shape), and it strictly subsumes what `opt_precise_inversion`
approximates today. The same rule applies to
hypotheses and goals (they go through `prop_to_formula`'s `Prod` case, which calls
`make_guard`), so a goal `forall s : {u : nat | u > 0}, P (proj1_sig s)` translates to
`∀s. nat(s) → s > 0 → P(s)` instead of an opaque `HasType(s, sig(…))`.

The expansion is an equivalence in the erasure model, so it is used at *both
polarities* — negatively for hypotheses/guards, positively for goals and
existentials (`exists s : {u | P u}, φ` becomes `∃s. nat-guard(s) ∧ P s ∧ φ'`).
No axiom is emitted for the rule itself; it exists only as translation-time
unfolding, like the existing `Π`-cases of `prop_to_formula`.

**The boundary of shallowness.** A subset type can also occur *nested inside* a
type-constructor application — `list {x : A | P x}`, or as a parameter
instantiation deep in another type. There the type occurs as a FOL *term*, and no
per-occurrence formula expansion is possible; this is not specific to subset types
(the same is true of `list nat`, TODO 6) and its systematic treatment is the
specialized-type-predicate / monomorphisation work of TODO 5/6
(`notes/monomorphisation.md`). For point 9 it suffices that (i) the term encoding
of a nested `sig A P` remains what it is today (so nothing regresses), and (ii)
once TODO 6 introduces specialized predicates `list_σ(x)`, the *definition* of the
specialized predicate for `σ = sig A P` is generated with the shallow rule above
(membership of the element type expands into carrier guard + spec formula), so the
two designs compose instead of colliding.

### 5.3 E3 — Singleton-content collapse: `sig A P ≅ A` (fixes G3)

Letouzey's singleton optimization, applied **at translation time, per occurrence** —
after E3 the symbols `sig`/`exist`/`proj1_sig` should simply not appear in the FOL
output for direct occurrences, mirroring how extraction makes them vanish from the
extracted program. (An earlier draft of this note proposed a "declarative layer" of
bridge axioms `∀A P x. exist(A,P,x) = x` as phase 1, leaving the rewriting to the
ATP. That is a deep embedding and is rejected for the reason stated in §4,
principle 4 — the
per-occurrence form is the *only* acceptable primary mechanism; TODO 5's remark
applies verbatim: doing it at the translation level is what lets the rest of the
output be optimised, e.g. spec predicates β-reduce against the collapsed value.)

Occurrence rules, for a `Subset`-classified instance:

- **Constructor spine** (`convert`): `exist A P v prf ↦ C(v)` — translate the spine
  to the translation of its informative argument (the proof argument is already
  dropped by `convert`, `coq_transl.ml:580-583`).
- **Match** (`case_lifting`): `match e with exist x h => s ↦ C(s[e/x, $Proof/h])` —
  substitute the matched term itself for the informative variable, `$Proof` for the
  proof variables. This makes `proj1_sig` literally the identity: its definitional
  axiom comes out as `$_def_proj1_sig : ∀A P e. proj1_sig(A,P,e) = e` — and better,
  *applied* occurrences `proj1_sig A P e` should be unfolded to `C(e)` during
  translation (δ-unfold identity-like projections of collapsed types), so goals
  mentioning `proj1_sig (h …)` translate straight to formulas about `h(…)`.
- **Partial applications** (a bare or under-applied `exist`/`proj1_sig` passed to a
  higher-order function): η-expand and let the existing lambda-lifting machinery
  handle it — the lifted fresh constant then gets its defining equation through the
  rules above (`∀x. F(x) = x`), generated only where such an occurrence actually
  exists. This is the same discipline the translation already uses for lambdas, and
  it is the only place a bridge-style equation legitimately appears.

Declaration-level consequences (in `add_def_axioms`, `coq_transl.ml:1065`, for
`Subset`-classified inductives): skip the constructor's injectivity axiom (vacuous
after collapse; also removes today's `$Proof = $Proof` conjunct in `$_inj_exist`),
skip its typing axiom (its realizability reading becomes a tautology of the §5.2
rule), and skip the ∃-form inversion axiom (subsumed by the inline guard expansion;
nothing selects `sig` as a premise anymore because nothing mentions it).

Net effect on the running example: `$_def_h : ∀x y z. h(x,y,z) = z` directly
(E1 erases the `and`-match, E3 collapses `exist(…, z)` to `z` in the same
translation pass) — the exact definitional equation displayed in TODO 9, with no
`exist`, no `sig`, and no ATP rewriting needed to see it.

### 5.4 E4 — Per-instance handling of sort-ambiguous type formers (fixes G4)

The JAR paper §9 suggests four copies of `prod`; with untyped FOL and per-occurrence
guards we do not need copies at all. The classification of §5.0 is *instance*-based:
at each guard/inversion/case site we classify `I p̄` with the actual parameters. What
this yields, with no further mechanism:

- `A * B` with `B : Prop` → `Subset(A, [B])`: guards become `T(w,A) ∧ B'`; `pair`'s
  proof component is already dropped by `convert`; §5.3(b) collapses
  `pair(A,B,a) ↦ a` and `fst ↦ id`; `snd p` is a proof, already `$Proof`.
- `A * B` with both propositions → `Enum`: the value is the constant `pair(A,B)`;
  inversion gives `HasType(w, prod(A,B)) → A' ∧ B' ∧ w = pair(A,B)`.
- `{A} + {B}` (`sumbool`) → `Enum`: inversion
  `HasType(w, sumbool(A,B)) → (w = left(A,B) ∧ A') ∨ (w = right(A,B) ∧ B')` — this
  makes decision procedures (`eq_nat_dec`, `le_lt_dec`, ...) *specified*, a large
  class of currently-unusable premises. Matches on `sumbool` values already work via
  the non-Prop `case_lifting` branch; the per-instance specs make the *results*
  meaningful.
- `A + {B}` (`sumor`), `sigT` with propositional family, `option`-style mixtures: fall
  out of the same classification, `Regular` cases unchanged.

The only implementation requirement is that classification happen at *occurrence*
sites (guard computation, inversion instantiation, case translation), keyed by the
propositionality mask of the actual parameters — the oracle (`check_prop`) and the
call sites all exist. Conceptually (per `notes/extraction.md` §5.2): the JAR paper's
"four definitions of `prod`" are just the four per-instance unfoldings of one
simulation-predicate transformation, so with instance-level classification the
variants problem dissolves rather than being solved by duplication.

### 5.5 Companion change: per-constructor match axioms (TODO 7)

Not part of point 9, but designed in detail in `notes/extraction.md` §2 and strongly
synergistic: replacing the guarded disjunction-of-existentials match axiom by
per-constructor (conditional) equations turns definitional axioms into orientable
unit/near-unit rewrite rules. Composed with this design: E1's erased singleton
matches already produce single equations; the split form then makes `h(x,y,z) = z`,
`eq_rect(…) = x`, and the `Subset` collapse equations pure unit equations —
demodulators for superposition provers, ideal triggers for SMT. The two changes
share the `case_lifting` implementation site and should be sequenced as in
`notes/extraction.md`'s incremental path (split first — self-contained and
independently measurable — then E1/S/E3). The guard analysis there (§2.3: the split
form makes no exhaustiveness claim, so the currently *mandatory* guards on the
matched term's free variables become unnecessary) also simplifies the guard policy
of §5.1.

### 5.6 What is *not* proposed

- **Routing through Letouzey's MiniML IR** (the JAR paper's own suggestion): rejected
  as a literal code-reuse plan. Extraction's IR erases the specifications we need to
  keep, its API is not stable across Rocq versions, and §5.1–5.4 reuse the existing
  `coqterm` pipeline with strictly local changes. The *conceptual* factoring is
  adopted wholesale (§4.1); and a longer-term in-repo refactor toward an explicit
  `Cic₂`-style erasure-annotated IR — so that `check_prop`/proof-variable decisions
  happen once, before lifting, instead of being re-derived throughout
  `convert`/`case_lifting`/`make_guard` — is a reasonable phase-5 cleanup
  (`notes/extraction.md` §5, step 4), distinct from reusing extraction's code.
- **Equations-style elaboration** (graph + functional elimination): too heavyweight,
  requires per-definition elaboration; but when a definition *has* Equations-generated
  equations in the environment, premise selection will pick them up as ordinary lemmas
  — no special support needed.
- **A HOL intermediate stage** (TODO 12) is orthogonal: everything here concerns what
  FOL *content* is emitted, not the logic pipeline's factoring.

---

## 6. Soundness discussion

The translation is deliberately "sound enough" rather than sound (JAR §5.6): it
already assumes proof irrelevance, forgets universes, maps `eq` to FOL `=`, and omits
guards for lifted free variables. The design keeps all new axioms **true in the
proof-irrelevant erasure model** (§4.2). Per rule:

- **E1 on `and`/`True`**: the erased branch uses the destructed proofs only as
  proofs; the equation holds unconditionally in the model. Uncontroversial.
- **E1 on `Acc` (recursion through the proof)**: the unconditional equation is
  **false in the term model** (the erased term is a diverging/stuck closure at
  arguments violating the precondition, not a solution of `x = S x`) and
  inconsistent with ordinary premises such as `n_Sn`. The erased `Prop`
  preconditions are therefore kept as mandatory implication premises (§5.1) —
  the "recursive realizability" form, not the "modified realizability" form, in
  the terminology of `notes/extraction.md` (which traces the same distinction to
  the evaluation-order problem that shaped Letouzey's `E`). With the premises
  kept, the conditional equation is a genuine Coq theorem (provable by `Fix_eq` /
  functional induction), so this case is *sounder* than the `eq` case.
- **E1 on `eq` (transport erasure)**: `eq_rect(A,a,P,x,b) = x` is the extraction
  semantics, but as a *Coq* statement `∀e:a=b. eq_rect … = x` is `eq_rect_eq`,
  i.e. UIP/K on `A` — not provable in general (Gilbert et al. 2019), provable for
  decidable-equality types (Hedberg). Consequences: (i) the FOL problem stays
  consistent relative to the model (PI validates K-like collapse propositionally at
  erased positions); (ii) an ATP proof that *essentially* uses the unconditional
  equation at a non-UIP type may fail reconstruction. This is the same failure mode
  the tool already has for functional extensionality, and it is why reconstruction is
  the safety net. `opt_erasure_guards` (§5.1) provides the conservative variant
  (`a = b → eq_rect(…) = x`), which is provable in Coq by destructing the equation
  *when the equation is available propositionally* — evaluate both; default to
  unguarded (matching TODO 9's requested output) unless evaluation says otherwise.
- **S/E3 (subset collapse)**: the inline guard expansion (`T(w,A) ∧ P w` in place
  of a `sig` atom) and the occurrence collapse (`exist(A,P,x) ↦ x`) together
  quotient `sig` values by proof components. In Coq,
  `exist x p = exist x q` requires proof irrelevance — already assumed globally by
  the translation (`$Proof`). The direction used by reconstruction-relevant goals
  (`proj1_sig`-style reasoning) is provable in plain Coq
  (`proj1_sig_eq`, `sig_ind`, `proj2_sig`), so reconstruction risk is low.
- **E4 (`Enum`)**: inversion with spec conjuncts is the image of the existing
  (sound-in-the-model) inversion scheme; nothing new.
- **Consistency hygiene**: the JAR paper's §5.6 example shows omitting guards for
  matched *non-proof* variables can create inconsistency; E1 concerns matched *proof*
  variables only, where the branch value cannot depend on the proof (all binders are
  proofs), so the analogous inconsistency does not arise — except through `eq`-erasure
  interacting with `eq ↦ =`, covered by `opt_erasure_guards` above.

A worthwhile follow-up (not blocking): extend the TYPES 2016 piPTS soundness proof
with singleton inductive elimination and subset types, in a piPTS + ι-reduction
setting. The rules were chosen so that each is the image of a theorem of the
extraction-correctness literature (Letouzey ch. 2; Paulin-Mohring's realizability
adequacy), so the extension is plausible pen-and-paper work.

---

## 7. Implementation plan

Phased so that each phase is independently mergeable, testable, and ablatable.

**Phase 0 — infrastructure.**
- `coq_erasure.ml` (or extend `coq_typing.ml`): instance classification of §5.0,
  memoized on `(inductive, param mask)`; unit-testable via `Hammer_transl`.
- Treat `SProp` exactly like `Prop` in `to_coqsort` (`coq_convert.ml:31-35`) and
  `check_prop`/`check_proof_var` (`coq_typing.ml:177-296`); today SProp hypotheses
  fall through to `Type` handling. (Small, independent correctness fix.)
- New options in `coq_transl_opts.ml`:
  `opt_prop_case_erasure` (E1, default true),
  `opt_erasure_guards` (guarded E1 equations for the `eq` case, default false),
  `opt_subset_types` (S + E3 + E4 as one unit — the shallow expansion and the
  occurrence collapse are two halves of the same erasure and are not meaningful
  separately; default true).
  Wire through `tacopts.ml`/`g_hammer.mlg` if user exposure is wanted (not required
  initially — these are translation options, not tactic options).

**Phase 1 — E1 (case erasure), the core fix.**
(If TODO 7's per-constructor split axioms are pursued, do them first or in the same
series — same implementation site, independently measurable; see §5.5 and
`notes/extraction.md` §2.7.)
- `case_lifting` (`coq_transl.ml:411`): implement §5.1. The `PropSingleton` path
  peels branch lambdas (they carry their domain types in `Lam(name,ty,body)`),
  applies `subst_proof`, and reuses the equation-emission code currently in
  `lambda_lifting`'s default branch (factor it out) so `axname` fires. Recursion
  through nested matches mirrors `hlp` (`coq_transl.ml:467`).
- Detect the recursion-through-proof pattern (fix whose decreasing argument is
  propositional, or an erased match under such a fix): either keep `generic_match`
  for it in phase 1a, or (1b) emit the conditional equation with the enclosing
  definition's erased `Prop` hypotheses as premises (§5.1's mandatory guard rule),
  reusing the `opt_lambda_guards` code path per-definition.
- Acceptance: `Hammer_transl "h"` prints `$_def_h : ∀xyz. h(x,y,z) = exist(…, z)`
  (collapse comes in phase 2); `tr` gets `eq_rect` equations making
  `tr(P,a,b,x) = x` derivable; a `Function`-defined `gcd` gets a *conditional*
  recursive equation with its `Prop` preconditions as premises, and the translation
  of wf-division must NOT make `div a O = S (div a O)` derivable (add a
  translation-level test asserting consistency of the emitted axiom set on this
  example, e.g. by running an ATP on it briefly with a `$false` conjecture).

**Phase 2 — S + E3 + E4 (specification extraction + singleton collapse, one unit).**
- `make_guard` / `type_to_guard` inline expansion rules (§5.2), β-simplifying spec
  predicates before conversion; suppress `opt_type_lifting` for types with erasable
  content and emit the applied ∀-form spec axiom (§5.2).
- Occurrence collapse in `convert`/`case_lifting` for `Subset` instances, including
  δ-unfolding of identity-like projections and η-expansion of partial applications
  (§5.3). These land together with the guard rules: the shallow spec formula
  `x = h(x,y,z)` only exists because the collapsed value *is* `h(x,y,z)`.
- Declaration-level skips in `add_def_axioms` (`coq_transl.ml:1065`) for
  `Subset`-classified inductives: no injectivity/typing/∃-inversion axioms for
  collapsed constructors (§5.3).
- Per-instance classification at guard/inversion/case sites (§5.4).
- Acceptance, on `Hammer_transl "h"` output *literally*:
  `$_def_h : ∀x y z. h(x,y,z) = z` and a spec axiom containing
  `x=y ∧ y=z → … x = h(x,y,z)`; the symbols `sig`, `exist`, `proj1_sig` and any
  `HasType(…, sig(…))` atom are **absent** (grep-style assertion, like
  `tests/plugin/transl.v`); `sumbool` premises (`eq_nat_dec`) become usable.

**Phase 3 — cleanups.**
- Filter `$Proof = $Proof` conjuncts from injectivity axioms (independent cleanup).
- Optional: emit *nothing* for `Empty` matches reachable only under refuted
  inversion disjuncts.

**Phase 4 — adjacent unblockers (separate commits, same theme).**
- Primitive projections (`$Proj`, `coq_convert.ml:175`): translate as the
  corresponding compatibility constant application. Without this, record-heavy
  developments (MathComp) never reach the new machinery.
- Reconstruction interplay: new axioms must carry the *originating constant* as their
  label (the axiom-label mechanism used by `provers.ml` dependency extraction), so
  ATP proofs using `$_def_h`/`$_typeof_h` report `h` and `tacbest`/`sauto` will
  unfold/destruct it. If evaluation shows reconstruction lagging on subset-type
  proofs, add `proj2_sig`/`sig_ind`-style lemmas to the reconstruction context when
  a `Subset`-classified constant appears in the dependency list (hook: the
  `atp_info` plumbing from TODO 4).
- Premise selection: no changes needed (`features.ml` reads raw `hhterm`s), but note
  that newly meaningful definitions enrich `D(T)` dependencies for free.

**Tests.** `tests/plugin/` currently has *no* dependent-type fixtures. Add
`tests/plugin/deptypes.v` with at least: the `h` example (prove
`forall x y z p, proj1_sig (h x y z p) = z` and `x = proj1_sig (h x y z p)` by
`hammer`); an `eq_rect` transport goal; a `Function`/`Program Fixpoint` recursive
equation goal; a `sumbool` premise goal (`Nat.eq_dec`); a `sig2`/`prod`-with-Prop
instance. Mirror the `transl.v` sanity-grep pattern to assert `$_def_h` and the
absence of `$_generic_case` in `Hammer_transl "h"` output.

---

## 8. Evaluation plan

Use `eval/` (see `eval/README.md`) on the standard library and at least one
dependent-type-heavy target (e.g. a `Program`/`Function`-using development;
stdlib `FMaps`/`MSets` use `sumbool`/`sig` heavily; CompCert-style code if licensing
permits; MathComp only after Phase 4's primitive projections).

Measure, per phase and per option flag (ablation):

1. Number of definitions that gain a `$_def_*` equation (static count over the
   problem set) — direct measure of G1 closure.
2. ATP success rate (Vampire/E/Z3, fixed premise counts) vs. the `rocq-9.1` baseline.
3. Reconstruction success rate on newly-found proofs (detects soundness-debt abuse:
   a spike in ATP-success without reconstruction-success on `eq_rect`-heavy problems
   would argue for `opt_erasure_guards := true`).
4. Problem-size impact (axiom count / TPTP bytes) — S/E3 should *shrink* problems
   (inline spec formulas replace ∃-inversion detours; the occurrence collapse
   removes the `sig`/`exist`/`proj1_sig` symbols and their support axioms
   entirely).

Success criterion: no regression on the FOL-ish stdlib bulk, and a strict improvement
on the dependent slice (goals mentioning `sig`/`sumbool`/`eq_rect`/wf-recursion),
which currently sits near zero by construction.

---

## 9. Expected impact

- **Well-founded / `Program` / `Function` definitions** become equationally visible
  (E1, in the conditional-equation form mandated by §5.1). Currently *every* such
  function is a fresh constant with an opaque type.
- **Transport-heavy dependent code** (`eq_rect` and friends) stops poisoning every
  premise that touches it (E1).
- **Subset-typed APIs** (`sig` in stdlib interfaces, `sumbool` decision procedures,
  strong specifications à la `{q | a = q*b + r ∧ r < b}`) become first-class:
  the type *is* the lemma, and specification extraction turns it into one (S/E3/E4).
- The three sub-problems of TODO 9 (dependent functions, propositional case analysis,
  `sig`/`prod`/`sum` with propositional arguments) are covered by one mechanism —
  extraction-guided erasure + realizability-guided specification — rather than three
  special cases, and the mechanism has a clear semantic model and literature anchor.

Main risks: (i) `eq`-erasure reconstruction failures → mitigated by
`opt_erasure_guards` and measured by eval metric 3; (ii) axiom bloat from guard
equivalences on rarely-used types → mitigated by emitting subset-type axioms lazily
(only when the type occurs in the problem — the `Defhash`-driven laziness already
gives this for free); (iii) interaction with the arity/`$HasType` optimizations
(`opt_type_optimization`, `opt_multiple_arity_optimization`) — the new guard forms
must go through the same post-processing; covered by the `transl.out` sanity check
plus new grep assertions.

---

## 10. References

- Ł. Czajka, C. Kaliszyk. *Hammer for Coq: Automation for Dependent Type Theory.*
  J. Automated Reasoning 61(1–4), 2018. doi:10.1007/s10817-018-9458-4. (Translation:
  §5; limitations relevant to TODO 9: §9.)
- Ł. Czajka. *A Shallow Embedding of Pure Type Systems into First-Order Logic.*
  TYPES 2016, LIPIcs 97, 2018. doi:10.4230/LIPIcs.TYPES.2016.9. (Sound piPTS core;
  ε-erasure of proofs.)
- P. Letouzey. *Programmation fonctionnelle certifiée: l'extraction de programmes
  dans l'assistant Coq.* PhD thesis, Université Paris-Sud, 2004.
  HAL: https://theses.hal.science/tel-00150912 (English translation:
  https://www.irif.fr/~letouzey/download/these_letouzey_English.ps.gz).
  Key sections for this design: §2.2 (erasure `E`), §2.4 (simulation predicates
  `⟦·⟧₂`/`Î`; div example §2.4.4 — the model for §5.2 here), §2.6 (empty inductives,
  singleton elimination), §4.3 (logical-argument pruning, informative singleton
  unboxing with its non-recursive-carrier side condition — the model for §5.3).
- P. Letouzey. *A New Extraction for Coq.* TYPES 2002, LNCS 2646.
  https://www.irif.fr/~letouzey/download/extraction2002.pdf (singleton criterion
  and elimination rule; the `cast` example; restrictions (i)–(iii), of which (iii)
  is the well-founded-recursion constraint of §5.1/§6).
- P. Letouzey. *Extraction in Coq: an Overview.* CiE 2008, LNCS 5028.
  https://www.irif.fr/~letouzey/download/letouzey_extr_cie08.pdf
- C. Paulin-Mohring. *Extracting Fω's programs from proofs in the Calculus of
  Constructions.* POPL 1989. (Realizability translation — the model for §5.2.)
- G. Gilbert, J. Cockx, M. Sozeau, N. Tabareau. *Definitional Proof-Irrelevance
  without K.* POPL 2019. (SProp; limits of irrelevance vs. K, relevant to §6.)
- Y. Qian et al. *Lean-auto: An Interface between Lean 4 and Automated Theorem
  Provers.* CAV 2025, arXiv:2505.14929. (Equational lemmas + monomorphization as the
  ATP currency for dependent definitions.)
- A. Šinkarovs, M. Rawson. *When Agda met Vampire.* arXiv:2602.18844, 2026.
  (Equational-Horn shared fragment between dependent type theory and FOL ATPs.)
- J. Meng, L. Paulson. *Translating higher-order clauses to first-order clauses.*
  JAR 40(1), 2008. J. Blanchette, S. Böhme, A. Popescu, N. Smallbone. *Encoding
  monomorphic and polymorphic types.* LMCS 12(4), 2016. (Type-guard/tag encodings and
  their soundness; reference point for guard-omission options — see
  `notes/type_guards.md`.)
- T. Tammet, J. M. Smith. *Optimized encodings of fragments of type theory in
  first-order logic.* J. Logic and Computation 8(6), 1998. (Conference version:
  TYPES '95, LNCS 1158 — text in
  `notes/papers/tammet-smith-1996-optimized-encodings-type-theory-fol.txt`.)
- F. Wiedijk. *Mizar's Soft Type System.* TPHOLs 2007. (Types-as-predicates; subset
  types as adjectives.)
- M. Sozeau, C. Mangin. *Equations Reloaded.* ICFP 2019. (Elaboration of dependent
  pattern matching; equations + functional elimination as an alternative spec source.)
- This repo: `notes/extraction.md` (TODO 7 per-constructor match axioms; thesis
  digest; clause-shape analysis; the well-founded-recursion caveat adopted in §5.1;
  incremental path §5).
