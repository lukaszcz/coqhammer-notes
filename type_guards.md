# Omission of inferrable type guards and of type arguments (TODO points 3 and 2)

*Investigation notes, 2026-07-05. Sources: `src/plugin/coq_transl.ml` (this repo);
Czajka & Kaliszyk, "Hammer for Coq: Automation for Dependent Type Theory", JAR 61,
2018 (the JAR paper, §5); Czajka, "A Shallow Embedding of Pure Type Systems into
First-Order Logic", TYPES 2016 post-proceedings, LIPIcs 97 (the PTS paper, esp. the
§6 remarks on guard omission); Blanchette, Böhme, Popescu & Smallbone, "Encoding
Monomorphic and Polymorphic Types", LMCS 12(4), 2016; Claessen, Lillieström &
Smallbone, "Sort It Out with Monotonicity", CADE 2011; Meng & Paulson, "Translating
Higher-Order Clauses to First-Order Clauses", JAR 40, 2008; Bobot & Paskevich,
"Expressing Polymorphic Types in a Many-Sorted Language", FroCoS 2011; Urban's MPTP
papers; Letouzey's PhD thesis (2004); the Rocq reference manual chapter on CIC
typing rules; `notes/extraction.md` (this repo). All concrete FOL outputs below were
produced with `Hammer_transl`/`hammer_transl` using the plugin built from this
branch (Rocq 9.1.1).*

> **Paper version:** a mathematically rigorous formulation of the criteria of
> §3.3 (tier A) and §4, with full soundness/conservativity proofs for a
> polymorphic first-order fragment of CIC and tightness counterexamples, is in
> `notes/type_guards/` (`main.tex`; build with `just` — drives `xelatex`).
> Differences from these notes: the paper additionally proves the existential
> guard equivalence under the dual junk-*falsity* judgment (so the ∃-conjunct
> guard in `le`-inversion is droppable as an equivalence, not just kept as a
> fact), and it shows the notes' "dually for ∃ under JV" claim in §3.3 is
> wrong as stated (junk-truth does **not** license dropping an ∃-guard: see
> the `void` counterexample, Prop. 8.2 in the paper).

## TL;DR

1. **TODO 3 admits a principled, general criterion.** Call an atom *strict* if, in
   the intended ("standard") model of the translation, it is false whenever one of
   its arguments is not of the type forced by the head symbol's declared type
   (predicate applications such as `Even(x)`, `le(n,m)`, `In(A,x,l)` and rigid
   `$HasType` atoms are strict; *equations are not*, and neither are atoms headed
   by translation-generated symbols such as `$_prop_N` or `$HasType(_, $_type_N …)`).
   Then a guard `HasType(x,τ)` on a quantified variable may be omitted whenever the
   guarded body is **junk-vacuous**: true (in the intended model) under every
   ill-typed instantiation of `x` — for which a simple syntactic sufficient
   condition is that the body contains, in hypothesis position, a strict atom with
   `x` at a position forcing type `τ`. This is exactly the TODO's `Even(x) ⇒
   nat(x)` example, it is polarity-independent (an *equivalence* in the intended
   model, applicable to premises and goal alike), and it is provable correct for
   CIC-minus-the-known-caveats by pure typing inversion — no canonicity, no
   consistency, and no monotonicity analysis needed (§3). It is the dependent-type
   analogue of the *cover-based guards* (`g@`) of Blanchette et al., whose
   soundness proof it mirrors, and it lands precisely in the gap that the PTS paper
   leaves open ("adapting monotonicity inference to embeddings of constructive
   dependent type theory into FOL" is posed there as an open problem).

2. **TODO 2 also has a standard answer in the literature**: a type argument of a
   constant is omittable when it is *inferable/covered* — it occurs *rigidly* in
   the type of a retained term argument (Blanchette et al.'s `a^ninf` filter with
   covers; Letouzey's extraction drops inductive parameters of constructors
   unconditionally for the same reason, and his §3.5.1 states the criterion
   verbatim: such arguments "can be removed, since we know how to identify them in
   all cases, purely by typing"). So `cons A x l ⇒ cons(x,l)` (A read off `x`),
   but `nil A` keeps `A` (result-only). Coq's implicit-argument data
   (`Impargs.implicits_of_global`) is a good *proposal generator* but not a
   soundness criterion: Coq's elaboration also infers from the *expected/result*
   type, which is not available at a FOL occurrence (§4).

3. **The two optimizations interact and must be coordinated.** Erasing the type
   arguments of *predicates* destroys exactly the type-forcing positions that TODO
   3's criterion relies on (after erasing `A` from `In`, the atom `In(x,l)` no
   longer pins `x : A` for the quantified `A`). Recommended resolution: erase type
   arguments only of constants whose type target is not `Prop` (constructors and
   functions — where the term bloat actually is), keep predicate atoms fully
   applied (§4.3).

4. **The expected payoff is real and is documented across three independent
   evaluations** (Meng–Paulson, Blanchette et al., Bobot–Paskevich): guard/type
   clutter is strongly anticorrelated with ATP success, and cover-based/lightweight
   guard placement recovers nearly all of the (unsound) type-free encodings'
   success rate while staying sound. CoqHammer's premises are currently translated
   with *traditional full guards* on every quantifier — the encoding that performs
   *worst* in those comparisons (§2.3).

5. **Proposed implementation**: a self-contained post-processing pass over the
   generated `fol` formulas (between `translate` and `Tptp_out`), option-gated,
   with three levels for guards — A: drop strictly-covered guards
   (intended-model-equivalence-preserving, prove-ably safe); B: additionally place
   guards only on "naked or undercover" variables à la `g@`/`g??`
   (satisfiability-preserving, needs global uniformity); C (future):
   monotonicity-based — plus the type-argument erasure of point 2 (§5). Evaluate
   each on the `eval/` harness (§7). A test suite of known-unsoundness patterns to
   guard against is in §6.

---

## 1. Current state

### 1.1 Where guards come from

In the FOL output, a guard is an atom `$HasType(t, τ)` (`opt_hastype = true`;
otherwise `τ @ t`). Generation sites, with defaults (all in
`src/plugin/coq_transl.ml`):

| # | Site | Code | Guarded? | Shape |
|---|------|------|----------|-------|
| 1 | ∀/∃ in propositions (non-Prop domain) | `prop_to_formula` (:643), `convert` `Quant` (:545) | yes | `∀x. T(x,τ) → φ` / `∃x. T(x,τ) ∧ φ` |
| 2 | Prop-domain products | `prop_to_formula` (:647) | no quantifier | `F(τ) → φ`; proof var becomes `$Proof` |
| 3 | Typing axioms `$_typeof_c` | `add_typing_axiom` (:834) via `make_guard`/`type_to_guard` | yes | `G(c,τ)` unfolded: `∀x. T(x,A) → T(c x, B)`; functional types lifted to `$_type_N` (`opt_type_lifting`) |
| 4 | Type-definition axioms (`$_type_N`, defs of sort Set/Type) | `add_def_eq_type_axiom` (:821) | biconditional | `∀v. T(v, F ȳ) ↔ G(v, τ)`; the `∀ȳ` prefix itself is UNGUARDED |
| 5 | Lambda/fix/let/cast-lifted definitional axioms | `lambda_lifting` (:335), `close` (:719), `make_fol_forall` (:691) | **no** (unless `opt_closure_guards` / `opt_lambda_guards`) | `∀ȳx̄. F ȳ x̄ ≈ body` |
| 6 | Free vars of a case scrutinee | `add_inversion_axioms0` (:294) + `mk_guards` (:279) on `get_fvars matched_term` (:326) | **yes, mandatory** (JAR §5.6 counterexample) | `guards_{fvars(t)}(disjunction)` |
| 7 | Inversion axioms per inductive | `add_inversion_axioms` (:1032) | yes | `∀p̄ȳz. T(…) → T(z, I p̄ ȳ) → disjunction`; ∃-bound constructor args get guard conjuncts |
| 8 | Prop-inversion axioms | `mk_prop_inversion` (:236) | yes | `∀p̄ȳ. T(…) → I p̄ ȳ → disjunction` |
| 9 | Injectivity / discrimination axioms | `add_injection_axioms` (:918), `add_discrim_axioms` (:974) | **no** (`opt_injectivity_guards` / `opt_discrimination_guards` = false) | note `$_inj_nil` even asserts parameter injectivity `nil A = nil A' → A = A'`, not a CIC theorem but true in the syntactic term model |
| 10 | Lifted-proposition equivalences `$_prop_N` | `convert_term` (:617) | **no** | `∀ȳ. P(F ȳ) ↔ φ` |

Only `opt_closure_guards` is a runtime option (`Set Hammer ClosureGuards`,
`src/plugin/opt.ml:195`). `Axhash` caches per-constant translations across
queries, so any new runtime-settable translation option must invalidate that
cache.

### 1.2 Where type arguments come from

The translation keeps every Coq argument of every constant (minus proof arguments,
which become `$Proof` and are dropped from applications by `convert`, and minus
the type argument of `eq`, dropped by `adjust_logops` — an existing precedent for
point 2). So polymorphic applications carry their type arguments as first-class
FOL terms: `cons nat 0 l` ⟶ `cons(nat, 0, l)`, `In nat x l` ⟶ `In(nat, x, l)`.
The Meng–Paulson arity optimization (`tptp_out.ml`) then chooses concrete arities
but never removes arguments.

### 1.3 Concrete outputs (verified on this branch)

Goal `forall x : nat, Nat.Even x -> Nat.Even (S (S x))`:

```
∀x. T(x,nat) → Even(x) → Even(S(S(x)))
```

— the TODO 3 example verbatim; the guard is covered by the `Even(x)` hypothesis.

Goal `forall (x:nat) (l:list nat), In x (x :: l)`:

```
∀x. T(x,nat) → ∀l. T(l, list nat) → In(nat, x, cons(nat, x, l))
```

— here `x`, `l` occur only in the *conclusion* atom: **not** omissible by the
redundancy criterion (§3.3), only by the more aggressive tier B (§3.4). (As this
is a goal, dropping its guards is sound but discards usable facts; see §5.5.)

`$_inversion_Corelib.Init.Peano.le` (premise):

```
∀n m. T(n,nat) → T(m,nat) → le(n,m) →
  ( m = n  ∨  ∃k. T(k,nat) ∧ le(n,k) ∧ m = S(k) )
```

— both ∀-guards covered by the hypothesis `le(n,m)`; the ∃-conjunct `T(k,nat)` is
a provided *fact*, not an obligation (dropping it only weakens the axiom; keep by
default, §5.2).

`Stdlib.Lists.List.app_nil_r`:

```
∀A. T(A,Type) → ∀l. T(l, list A) → app(A, l, nil(A)) = l
```

— the guard on `l` is **not** omissible by redundancy (`l` occurs *naked* on the
right of a positive equation; the guard-free axiom is false in the intended model
and is precisely the pattern that Blanchette et al.'s "undercover variable"
analysis keeps guarded). The guard on `A` *is* omissible: it is covered by the
retained guard atom `T(l, list A)`, which is strict and forces `A : Type` by
typing inversion on `list A`.

`$_def_Stdlib.Lists.List.In` (unfolding of a Fixpoint over `l`): guards on `A` and
`l` are **not** omissible — the body asserts `l = nil A ∨ ∃… l = cons A …`, which
is false for junk `l`, not vacuous. Structural-recursion unfoldings are
inversion-like: their scrutinee guards are load-bearing (cf. §1.4). (They would
stop being needed under the per-constructor split axioms of TODO 7 — see
`notes/extraction.md` §2.3.)

### 1.4 What is already omitted, and on what grounds

The translation already omits guards in three places (sites 5, 9, 10 above; plus
no guards for the global environment prefix, PTS paper Example 46), with the
following theoretical status:

- The **JAR paper §5.6** reports that omitting closure/lambda guards "slightly
  improves the success rate of the ATPs without significantly affecting the
  reconstruction success rate", conjectures it sound *provided `eq` is not
  translated to FOL equality*, and notes the combination with `eq` = FOL `=` is
  unsound (functional-extensionality-style inconsistencies), hence the
  `Set Hammer ClosureGuards` escape hatch.
- The JAR paper's **case-scrutinee counterexample** (§5.6) shows guards on free
  variables of a matched term can *never* be dropped: for `I(c : Set := c0 : c)`,
  the guard-free case axiom `∀x. x = c0 ∧ F x = c0` is inconsistent with any two
  provably distinct constants. The deep reason (also `notes/extraction.md` §1.3):
  the disjunction makes an *exhaustiveness* claim, false for junk elements.
- The **PTS paper** proves soundness of a core guarded translation
  *proof-theoretically* (Theorem 75): its Lemma 74 harvests, from the FOL
  sub-proofs of guard atoms, the evidence that each first-order instantiation
  encodes a well-typed term — guards are the *only* channel through which the
  reconstruction learns typability. The single sanctioned omission (`Δ_Φ` axioms,
  lifted propositions) is justified there by: the variables "all occur in the
  target atom `P(f ȳ)` which in the soundness proof is assumed to encode a
  well-typed term". Omission of closure guards is stated as an expectation, not a
  theorem, and adapting model-theoretic monotonicity methods is flagged as an
  open problem ("the methods of the cited papers are model-theoretic, so they are
  probably not useful in our setting").

So the state of the art within CoqHammer is: guards omitted where lifted-out
terms are already well-typed (heuristic, conjectured sound), mandatory where
formulas make exhaustiveness/equational claims about a variable. What is missing
— and what TODO 3 asks for — is a *criterion* separating the two, applicable to
the biggest remaining guard population: quantifier guards in translated
statements and inversion axioms.

---

## 2. What the literature provides

### 2.1 Type encodings for hammers: covers, naked variables, monotonicity

Blanchette–Böhme–Popescu–Smallbone (LMCS 2016) is the definitive treatment, in
the setting of rank-1 polymorphic FOL translated to untyped FOL. Their concepts
map onto CoqHammer as follows (details in §3–§4):

- **Inferable type argument** (their Def. 34): `α_j` of
  `s : ∀ᾱ. σ₁ × … × σₙ → ς` is inferable if it occurs in some argument type
  `σᵢ`. Their `g` encoding (guards + `a^ninf` filter) *omits all inferable type
  arguments* and is sound and complete (their Thm. 38) — no monotonicity analysis
  needed, only that types denote disjoint domains and type constructors are
  interpreted injectively (their Lemma 45: covers determine the omitted type
  interpretation uniquely).
- **Cover** (Def. 40): a set of term-argument positions of `s` from which all
  inferable type arguments can be read off. **Undercover variables** (Def. 42): a
  variable occurring at a cover position of its enclosing symbol, *or naked in a
  positive equation* (i.e. as a whole side). The `g@` encoding guards only
  undercover universal variables and is sound and complete (Thm. 46). Quote on
  the intuition: "It may seem dangerous to allow ill-typed terms to instantiate
  `Xs`, but this is not an issue because such terms cannot contribute
  meaningfully to a proof … What matters is that 'well-typed' terms are
  associated with their correct type and that 'ill-typed' terms are given at most
  one type."
- **Monotonicity** (Claessen–Lillieström–Smallbone; their §5–6): full type/guard
  erasure is sound for *monotonic* problems (every model extendable to
  all-infinite domains); a type is inferred monotonic if it is known infinite or
  no variable of that type occurs *naked in a positive equation*. The
  featherweight `g??` guards only naked variables of possibly-nonmonotonic
  types. The formal heart of the soundness proof (LMCS Thm. 71) is that **a
  guard is nothing but a false-extended predicate** — interpretable as false on
  all domain-extension junk. This encoding is not just a paper result: it is
  the *shipped default* in Why3 (`src/transform/encoding_guards.ml`, whose
  header cites "featherweight guards g??"; its guard-skip condition is
  literally "polarity known, variable universal, and (not naked in a positive
  equation, or type known infinite)").
- **Arbitrary predicates as guards** (CLS 2011, "calculus 2") — the direct
  formal ancestor of TODO 3's `Even(x) ⇒ nat(x)`: a hypothesis literal
  `¬Q(…,x,…)` guards `x` exactly like a type guard, *provided* `Q` can be
  globally assigned a **false-extension policy** — no axiom in the problem may
  force `Q` to hold of junk. Consistency of the policy assignment is decidable
  by one SAT call per sort (NP-complete). Caveat from their own evaluation:
  on Isabelle problems calculus 2 bought nothing over the naked-variable test —
  but Isabelle problems have few adjective-like predicates, whereas
  CoqHammer/Mizar problems are full of inductive predicates constraining their
  arguments' types, so the cost/benefit differs (§3.3 below makes this the
  centrepiece).
- **Empirics**: traditional full guards are the worst sound scheme; `g??`/`g@`
  recover most of the gap to the unsound light encodings; the effect grows with
  premise count ("the strong correlation between the success rates and the
  average number of symbols confirms the expectation that clutter — whether type
  arguments, tags, or guards — slows down automatic provers"). Meng–Paulson (JAR
  2008) measured the same 10–16 pp gap between fully-typed and constant-typed
  translations, and Bobot–Paskevich (Why3) between guards (`Grd`) and plain type
  arguments (`Exp`, sound under all-infinite domains — their Thm. 5).
- **Known unsoundness patterns** when type information is dropped naively:
  finite-type exhaustion (`∀x:two. x=a ∨ x=b` collapses the universe);
  instance confusion (`N ≥ 0 → N > 0` leaking from `nat` to `int`); the
  Bobot–Paskevich polymorphic-finiteness trick (`isUnit : α → o` with
  `∀x:α. isUnit(x) → ∀y:α. y = x` plus `∀x:A. isUnit(x)`), which defeats any
  axiom-filtering approach; and the QED-survey warning that *machine-learned
  premise selection finds and exploits inconsistencies* in large translated axiom
  sets — directly relevant to CoqHammer's kNN/NB selectors.

Mizar/MPTP is the system closest to CoqHammer's soft-typing situation (types as
predicates, relativized quantifiers). Its only systematic guard omission is for
the top type `set` (provably `True`) — the degenerate case of redundancy — but
it ships the entire typing hierarchy as explicit Horn "cluster" axioms
(`cardinal(X) ⇒ Ordinal-like(X)` — exactly the `Even ⇒ nat` shape) and gets its
performance from aggressive axiom-set minimization (570 → 73 formulas per
problem) rather than from guard surgery: a reminder that shipping *fewer typing
axioms* can matter as much as fewer guard literals. For contrast at the other
extremes: F\* keeps all `HasType` guards but *starves* them via SMT
patterns/fuel; Lean-auto drops guards entirely by monomorphizing to HOL and
leaning on kernel-checked reconstruction.

### 2.2 CIC metatheory: why "Even(x) implies nat(x)" is a theorem-grade fact

From the Rocq reference manual's typing rules (chapter "Typing rules"; inversion
facts are standard consequences, by induction on derivations, since Conv is the
only non-syntax-directed rule):

- **(I1) Application inversion**: if `E[Γ] ⊢ h a₁…aₙ : T` with `h` declared at
  `∀x₁:A₁…xₙ:Aₙ. B`, then `E[Γ] ⊢ aᵢ : Aᵢ[a₁…aᵢ₋₁]` (up to conversion) for each
  `i`.
- **(I2) Argument positions are rigid under cumulativity**: product subtyping
  (subtyping rule 5) requires *convertible* domains — cumulativity gives no slack
  at argument positions. So the type against which each argument is checked is
  the head's declared domain type up to `≈` (conversion) only. The exceptions are
  sorts themselves (a term of type `Set` also has type `Type(i)`; the translation
  already collapses `Set`/`Type` via `opt_set_to_type` and drops universe
  levels) and cumulative universe-polymorphic inductives (universe instances
  only — invisible after collapse).
- **(I3) Inhabitation forces index/parameter typing**: if `p : Even x` then
  `Even x` is well-typed, hence by (I1)+(I2) with `Even : nat → Prop`, `x : U`
  with `U ≈ nat`. **This needs no canonicity and no consistency** — it survives
  axioms in the environment, section variables, everything: it is pure typing
  inversion. (Canonicity-based arguments would *not* survive axioms; the
  criterion below deliberately never uses them.)
- Caveats to carry into any implementation: conversion includes
  δ/ζ/ι/η-unfolding, so "the forced type is `τ`" must be checked modulo whatever
  normalization the translation itself performs (`coq_typing.ml`'s NbE `eval`
  does whnf-style unfolding; comparisons should be made on translated,
  simplified types — see §5.2); `SProp` sits outside cumulativity (currently
  not handled specially by the translation anyway); `let` bodies participate in
  conversion.

### 2.3 The extraction viewpoint (Letouzey; cf. `notes/extraction.md` §5.3)

Letouzey's thesis supplies the type-theoretic counterpart of both TODOs:

- **Inductive parameters are unconditionally dropped from constructor
  applications** by extraction — even informative (e.g. `nat`-typed) ones — "the
  typing rules of the CCI ensure that these parameters cannot vary in the
  definition of the constructors … they bring no new computational content"
  (thesis p. 133); the ι-rule of his calculus already discards them, so the
  Chapter-2 simulation theorems (`t ~_T E(t)`, Thm. 9) cover this pruning. This
  is TODO 2 for constructors, "with a correctness proof already on the shelf" —
  but note his setting recovers parameters from the *ML type* of the term, a
  resource the untyped FOL side does not have; hence the cover restriction below.
- **Type extraction `Ê` and `Obj.magic` insertion** (thesis Ch. 3): the places
  where `Ê` produces the unknown type `⊤` — dependent positions, variable- or
  match/fix-headed type expressions, non-uniform parameters — are exactly the
  places where ML-style inference *cannot* reconstruct a type argument, i.e.
  where FOL-side omission of a type argument or guard loses information. His
  §3.5.1 states the omission criterion for type arguments of type constructors
  verbatim: they "can be removed, since we know how to identify them in all
  cases, purely by typing". And his disabled optimization #4 (p. 140) is a
  cautionary tale in exactly our direction: a transformation can be
  evaluation-sound yet rejected because it makes the result *less typed* —
  omissibility must be judged against (re)constructibility of the type
  information, not against reduction semantics alone.

---

## 3. TODO 3 — a principled criterion for omitting type guards

### 3.1 The intended model

Fix a well-formed global environment `E` (with axioms allowed). Define the
intended model `M` of a translated problem, following the semantics the JAR
paper's optimisations implicitly appeal to and making it explicit:

- **Domain**: closed CIC₀ terms (well-typed in `E`, plus the translation's
  primitive constants), quotiented by the conversion the translation respects
  (`=βειζ` with proof erasure; all `Γ`-proofs identified with `prf`).
- `@` is interpreted as application (of the quotient classes).
- `P(t)` holds iff `t` denotes a well-typed proposition that is *inhabited* in
  `E`. In particular `P(t)` is **false when `t` is ill-typed**.
- `T(t, τ)` holds iff `τ` denotes a well-formed type and `t : τ` (up to
  cumulativity). In particular false when `τ` is not a type or `t` is not in it.
- `Equal(s,t)` is interpreted as equality of quotient classes. (This bakes in the
  `eq`-to-`=` translation and proof irrelevance; the known caveats — universe
  constraints dropped, funext-related closure-guard issues — are *orthogonal*
  to this note and inherited as-is.)
- Translation-generated constants (`$_lam_N`, `$_case_N`, `$_prop_N`,
  `$_type_N`, skolems): interpreted so as to satisfy their defining axioms; on
  "junk" (ill-typed) argument tuples their value is unconstrained.

The pragmatic soundness notion for the practical translation (the JAR paper's
"sound enough") is **truth in `M`**: every emitted premise axiom should be true
in `M`. A transformation of the axiom set is *safe* in this sense if it maps
`M`-true formulas to `M`-true formulas; then no FOL refutation can exist that
did not exist semantically before, and — what actually matters operationally —
the ATP does not start proving goals whose reconstruction is hopeless.

### 3.2 Strict atoms and type-forcing positions

**Definition (forced type).** Let `c` be a constant with (CIC₀) type
`∀y₁:B₁ … yₘ:Bₘ. B`. Argument position `j` of `c` *forces* the type
`Bⱼ[t₁…tⱼ₋₁]` at an occurrence `c t₁ … tₖ` (k ≥ j). By (I1)/(I2), in any
well-typed such occurrence, `tⱼ` has a type convertible to the forced type —
uniformly in the surrounding context, with no cumulativity slack (sorts and
universe-polymorphic instances excepted, both already collapsed by the
translation).

**Definition (strict atom).** A FOL atom `A` is *strict at argument `t`* if
`M ⊨ A[v]` implies that `v(t)`'s denotation is well-typed at the forced type of
`t`'s position. Concretely:

- `P`-atoms `p(t₁,…,tₙ)` (after predicate optimization; before it,
  `P(c @ t₁ @ … @ tₙ)`) with `c` a *user constant of Prop-target type*: strict at
  every argument position — `M` interprets them as inhabitation of `c t̄`, which
  requires well-typedness of the whole application (I3).
- `$HasType(t, τ)` where `τ` is a sort, a variable, or a *rigid application*
  `I @ u₁ @ … @ uₖ` of an inductive/constant type former: strict at `t` (forcing
  `τ`), **and** strict at each `uᵢ` sitting at a forced position of `I` (typing
  inversion applies hereditarily: `T(l, list A)` true forces `list A` well-formed
  forces `A : Type`).
- **Not strict**: `Equal(s,t)` (junk equals junk happily; equality atoms force
  nothing); atoms headed by lifted constants `$_prop_N` (their defining
  equivalence quantifies unguarded, so they hold of junk whenever the lifted body
  happens to); `$HasType(t, $_type_N ȳ)` at the `ȳ` positions (the `$_type_N`
  biconditional makes `T(z, $_type_N junk)` *vacuously true* when the guard body
  is a guarded ∀ — lifted types are not rigid); `$HasType` whose type side is
  headed by a *defined* function that could reduce (non-rigid — conversion can
  rewrite it into anything); atoms headed by variables.

### 3.3 Tier A: redundant (covered) guards — the TODO 3 criterion

**Definition (junk-vacuous).** Let `x` be a variable, `τ` a type term. A formula
`φ` (in the fragment produced by the translation) is *junk-vacuous for `(x,τ)`*
if `M, v ⊨ φ` for every valuation `v` sending `x` to an element not of type `τ`.
A sufficient syntactic condition `JV(φ)`, by recursion:

- `JV(G → ψ)` if `G` is a strict atom containing `x` at a position forcing `τ`
  — then `G` is false at junk, the implication vacuously true; (*the cover case*)
- `JV(G → ψ)` if `JV(ψ)` (weakening);
- `JV(∀y. ψ)` and `JV(∃y. ψ)` if `JV(ψ)` (the domain is nonempty);
- `JV(ψ₁ ∧ ψ₂)` if both; `JV(ψ₁ ∨ ψ₂)` if either;
- `JV(¬G)` and `JV(G ↔ G')` if `G`, `G'` are strict atoms covering `x` (both
  false at junk makes the equivalence true);
- nothing else (in particular: a bare atom, an equation, or an equivalence with a
  non-strict side is *not* junk-vacuous — no matter where `x` occurs in it).

**Criterion (Tier A).** In any formula of the problem, a guard implication
`∀x. HasType(x,τ) → φ ⇝ ∀x. φ` may be rewritten whenever `JV(φ)` holds for
`(x,τ)`.  **Correction (see the paper, `notes/type_guards/`):** the dual
rewrite of a guard conjunct `∃x. HasType(x,τ) ∧ φ ⇝ ∃x. φ` is **not**
licensed by `JV(φ)` — junk-*truth* of `φ` makes the unguarded ∃ strictly
weaker-to-prove, and e.g. for `τ` empty and `φ = ⊤` the rewrite proves a
false goal (paper, Prop. 8.2).  The ∃-rewrite is an `M`-equivalence exactly
under the dual junk-*falsity* condition `JF(φ)` (`φ` false under every
junk instantiation of `x`; e.g. `φ` a conjunction with a strict covering
atom as a conjunct, as in the `le`-inversion ∃-body).  With `JF`, dropping
the ∃-conjunct is safe and, given completion axioms, lossless.

**Proposition (safety).** If `JV(φ)`, then `∀x. HasType(x,τ) → φ` and `∀x. φ`
have the same truth value in `M` (and similarly for ∃). *Proof sketch*: elements
of type `τ` satisfy `φ` iff they satisfy the guarded body (the guard is true
there); junk elements satisfy `φ` by junk-vacuity, and satisfy the guarded
implication trivially. ∎

Consequences worth spelling out:

- **Polarity-independence.** Because this is an *equivalence in `M`*, it may be
  applied at any position of any premise *and of the goal* — it is a
  simplification, not a strengthening. This is stronger than what tier B (§3.4)
  or Blanchette-style encodings give (those are satisfiability-preserving
  encodings of whole problems, not per-formula equivalences).
- **What it does *not* preserve: FOL derivability.** `M`-equivalence does not
  mean the ATP can recover the dropped atom. A dropped guard was, depending on
  polarity, either an *obligation* (in a premise ∀-prefix: must be derived at
  each use — dropping it is pure win) or a *fact* (in the negated conjecture, or
  as an ∃-conjunct of a premise: was available to feed *other* remaining guard
  obligations — dropping it can lose proofs). Hence the policy in §5.2/§5.5:
  drop obligations, keep facts, and optionally emit *typehood-completion axioms*
  `∀x̄. p(x̄) → HasType(xᵢ, τᵢ)` (§5.6) which make the dropped information
  syntactically recoverable — these axioms are themselves `M`-true by (I3), so
  adding them is unconditionally safe.
- **Relation to CLS calculus 2.** Tier A is the dependent-type instance of
  "predicates as guards", with one simplification: CLS need a *global* SAT
  check that the covering predicate is consistently false-extendable, because
  their soundness lives at the satisfiability level. Tier A instead fixes one
  model `M` in which every strict predicate *is* false-extended by construction
  (ill-typed ⇒ uninhabited ⇒ false) and every emitted axiom is already true —
  so the false-extension policy is automatically consistent and no global check
  is needed. The price is that atoms which are *not* strict in `M` (`$_prop_N`,
  lifted types, equations) can never serve as covers, where CLS's SAT check
  might occasionally certify them; that generality is not worth the machinery
  here.
- **Relation to Mizar's cluster axioms.** The completion-axiom route (§5.6) has
  a purely proof-theoretic, intuitionistically robust reading used at library
  scale by MPTP: with the "conditional cluster" axiom `∀x. Even(x) → T(x,nat)`
  present (Mizar registrations like `cardinal ⇒ ordinal` are exactly this
  shape), the unguarded axiom is a *logical consequence* of the guarded one, so
  omission is conservative over "guarded problem + cluster axioms" — no model
  theory at all. This is the cleanest formulation for the eventual soundness
  proof: tier A omission = cluster-axiom addition (safe by (I3)) followed by a
  derivability-preserving simplification.
- **Relation to the PTS paper's proof-theoretic soundness.** Tier A has a natural
  proof-theoretic reading that matches Lemma 74's structure: when an ATP proof
  uses an instance of a guard-omitted axiom, the sub-proof of the covering strict
  hypothesis atom `p(…t…)` plays the role of the guard sub-proof — from a
  reconstruction of `p(…t…)` (Def. 73, case 1/2 of the PTS paper) one extracts a
  well-typed inhabitant of `p …t…`, and typing inversion (I3) yields the typing
  evidence for `t` that Lemma 74 previously read off the guard. Turning this
  sketch into a full extension of Theorem 75 (and extending that theorem to
  inductive types in the first place) is a research task; for the practical tool
  the `M`-truth argument plus reconstruction is the operative safety net, as it
  already is for the existing optimizations.

**Worked examples** (from §1.3):

| Formula | Guard | Verdict |
|---|---|---|
| `∀x. T(x,nat) → Even(x) → φ` | on `x` | drop — covered by strict `Even(x)`, position 1 forces `nat` |
| `le`-inversion | on `n`, `m` | drop both — covered by `le(n,m)` (note: `m = n` naked in a disjunct is irrelevant for tier A; junk-vacuity is established at the hypothesis `le(n,m)` before the disjunction is reached) |
| `app_nil_r` | on `l` | keep — body is an equation, no strict hypothesis |
| `app_nil_r` | on `A` | drop — covered by retained `T(l, list A)` at the rigid parameter position of `list` |
| `$_def_In` (fixpoint unfolding) | on `A`, `l` | keep — body is a disjunction of equations about `l` |
| `In_map`-style premise `∀A B f l x. … → In(A,x,l) → In(B, f x, map(A,B,f,l))` | on `A`, `x`, `l` | drop (covered by hypothesis `In(A,x,l)`: positions force `Type`, `A`, `list A`) — on `B`, `f` keep (only conclusion occurrences) |
| goal `In x (x::l)` | on `x`, `l` | tier A does not apply (conclusion-only occurrences); guards remain as facts |

Note the ordering discipline: covers may come from ordinary hypothesis atoms and
from *retained* guards, so compute a greatest fixpoint — start with all guards
droppable-if-covered, but a guard used as the sole cover for another must not
itself be dropped unless it has an independent cover (in the `app_nil_r` example,
`T(l, list A)` is kept for its own reasons and therefore covers `A`; if it were
droppable, `A` would need another cover, e.g. an `In(A,x,l)` hypothesis, which
also covers `A` directly). A simple two-pass scheme suffices: (1) mark guards
covered by non-guard strict hypotheses; (2) mark guards covered by guards not
marked in any pass; iterate to fixpoint (it's monotone and the formulas are
small).

### 3.4 Tier B: cover/naked-variable guard placement (the `g@`/`g??` analogue)

Tier A never drops a guard whose variable occurs only in equations or conclusion
atoms — e.g. `app_nil_r`'s `l`, or `∀x:nat. P(f x)` with no hypothesis. The
Blanchette et al. results say more is possible: with guards placed only on
**undercover variables** (occurring naked in a positive equation, or at a
type-inference-critical "cover" position) the encoding remains
satisfiability-preserving. The soundness argument is different in kind: one
*modifies* the model, reinterpreting symbols on junk tuples ("correcting" them to
arbitrary well-typed values), which works because *all* axioms are treated
uniformly, so nothing pins down junk behaviour. Adapted to CoqHammer:

- Guard kept iff the variable (a) occurs as a whole side of a positive `Equal`
  or under a positive `↔` between non-strict formulas, or (b) occurs at a
  position that a tier-A cover *of another retained guard* depends on, or (c)
  occurs in an inversion-like disjunction of equations against the variable
  (the case-scrutinee pattern — subsumed by (a) since those disjuncts equate the
  variable with constructor terms), or (d) tier C considerations apply (finite
  types; see below).
- This automatically reproduces every known data point: the mandatory
  case-scrutinee guards (naked in `x = cᵢ …`), the safe omission of closure
  guards for non-equational bodies, the JAR remark that closure-guard omission
  is dangerous *in combination with `eq`-as-`=`* (the danger cases are exactly
  equations with naked lifted-variable sides, e.g. `∀x. f(x) = x` from lifting an
  identity-like lambda — tier B would *keep* those specific guards, plausibly
  fixing the known funext unsoundness while keeping nearly all the benefit).
- CIC-specific caution: unlike the polymorphic-FOL setting, our "types" are
  first-class terms and `$HasType` participates in equality reasoning; the model
  surgery must also fix `$HasType` on junk (interpret it as false there — which
  is consistent because after tier B all typing axioms only *conclude* `HasType`
  of well-typed-shaped terms from guarded/covered premises). And finite types
  matter: `bool`-inversion's `X` is naked in `X = true ∨ X = false`, so its
  guard is kept by (a) — good, this is the Meng–Paulson two-element collapse
  otherwise.

Further tier-B cautions collected from the literature: variables of **Pi-type**
(function-valued) should be treated conservatively — their guards are nested
implications rather than simple `T`-atoms, and extensional collapse is the one
*documented* CoqHammer unsoundness (JAR §5.6); **possibly-empty types** matter
for completeness (the sound encodings ship inhabitation axioms exactly because
the model-restriction direction needs nonempty carve-outs; CIC types can be
empty, so tier B must not silently rely on inhabitation); and subsingleton /
exhaustion lemmas (`∀x:unit. x = tt`, `∀b:bool. b = true ∨ b = false`) are the
canonical naked-variable formulas whose guards the criterion must keep — they
are ordinary stdlib premises, not exotica.

Tier B should be strictly experimental until it has been through the eval
harness and the §6 test suite; unlike tier A it is *not* per-formula
`M`-truth-preserving (it asserts junk-instances that are false in `M`;
correctness lives at the whole-problem satisfiability level, and its
interaction with the `eq` translation deserves its own scrutiny). Its deployed
precedent (Why3's default `encoding_guards.ml`) is encouraging but lives in a
simply-typed, `eq`-free-of-funext setting.

### 3.5 Tier C: monotonicity-based omission (future work)

The full Claessen–Lillieström–Smallbone program — drop even naked-variable
guards for provably *infinite* types (`nat`, `list τ`, any inductive with a
recursive constructor), keep them only for possibly-finite ones — is what the
PTS paper poses as an open problem for the dependent setting. Infinity of an
inductive is decidable enough in practice (same criterion Isabelle/Why3 use),
and there is a nice twist available here: for inductives like `nat` the
translation *already emits* the injectivity and discrimination axioms from
which infiniteness is derivable inside the problem itself, which closes the
"infiniteness is only background knowledge" reconstruction gap Blanchette et
al. flag for their `Inf` sets.
Expected marginal gain over tier B is modest (tier B already leaves guards only
on equation-naked variables), and the interaction with `eq`-as-`=`,
`$HasType`-substitutivity and ML-driven premise selection makes the risk
profile worse. Park it until A and B are measured.

---

## 4. TODO 2 — omitting type arguments

### 4.1 Criterion

Let `c` be a constant or constructor with type `∀y₁:B₁ … yₘ:Bₘ. B`. Position `j`
(a *type* position: `Bⱼ` a sort or arity — Letouzey's "type scheme" test) is
**erasable** iff there is a retained *term* position `i` such that `yⱼ` occurs in
`Bᵢ` **rigidly**: at a forced argument position of a chain of inductive type
formers (e.g. `Bᵢ = yⱼ`, or `Bᵢ = list yⱼ`, or `Bᵢ = t yⱼ` with `t` an inductive
applied to closed args) — not under a defined function, a binder, or a
`match`/`fix` (where conversion or dependency destroys inference; these are
exactly Letouzey's `Ê = ⊤` positions and Blanchette et al.'s non-cover
positions). Erasure drops position `j` from *every* occurrence of `c` in every
emitted formula (uniformly — occurrences with fewer than `j` arguments keep their
prefix as-is; the semantic argument below is curried and does not require the
covering argument to be syntactically present at partial applications).

Standard consequences: `cons`'s parameter is erasable (read off the head, or the
tail); `nil`'s is **not** (result-only — Coq's elaborator infers it from the
*expected* type, which has no counterpart at a FOL term occurrence); `existT`'s
`A` is erasable via the witness, its `P` is not (occurs only under a product);
`None`'s is not; `pair`'s `A`,`B` are erasable. Constants distinguished *only* by
a type argument (`c : ∀A:Type. nat` patterns — Meng–Paulson's `card UNIV`
unsoundness) are automatically non-erasable, since a phantom/result-only
argument has no rigid occurrence in a term position.

`Impargs.implicits_of_global` should be used as a *filter on candidates* (erase
only positions Coq itself treats as implicit — matching user intuition and
keeping the output readable), never as the criterion: Coq marks `nil`'s argument
implicit (maximally inserted) precisely because elaboration uses the expected
type; erasing it in FOL conflates `nil nat` with `nil bool` as a *bare constant*,
inviting instance confusion in equations (`rev nil = nil` at different types).

### 4.2 Soundness sketch

The `M`-side interpretation of the erased `c` is
`I(c)(…dᵢ…) = I₀(c)(…, typeof_j(d̄), …, dᵢ, …)` where `typeof_j` reads the
`j`-th instantiation off the principal type of the covering argument (unique up
to the universe/cumulativity distinctions the translation has already erased —
`opt_set_to_type`, universe collapse; proof arguments are already `$Proof` and
never serve as covers). This is the CIC transcription of Blanchette et al.'s
Lemma 45 (uniqueness of the inferred type interpretation, from domain
disjointness + injectivity of type constructors): rigid inductive heads are
injective up to conversion, so the covering argument determines the erased
parameter, and every `M`-true axiom about `c` remains `M`-true about the erased
symbol. Formulas that *quantify* over the erased position (typing axioms,
inversion axioms) keep their quantifier and guards; only the term occurrences
shrink.

Consistency across axiom kinds (all must be rewritten by the same erasure):

- **Injectivity axioms**: `cons(A,x,l) = cons(A',x',l') → A=A' ∧ x=x' ∧ l=l'`
  becomes `cons(x,l) = cons(x',l') → x=x' ∧ l=l'` — the `A=A'` conjunct is
  dropped (it is anyway the parameter-injectivity claim that is not a CIC
  theorem; erasure removes the need to state it).
- **Discrimination axioms**: unchanged shape, fewer arguments.
- **Inversion axioms**: `T(X, list A) → X = nil(A) ∨ ∃h t. … X = cons(h,t)` —
  note `nil` keeps its argument, `cons` loses it; the `A` linkage survives
  through `T(h, A)`/`T(t, list A)` conjuncts (which are `M`-true and should be
  kept here — they are facts).
- **Typing axioms**: `∀A x l. T(A,Type) → T(x,A) → T(l, list A) →
  T(cons(x,l), list A)` — still `M`-true under the erased interpretation
  (given the collapse of universe distinctions, the type of a term argument
  determines the parameter).
- **Definitional axioms** (`$_def_*`, lifted equations): rewritten uniformly.

### 4.3 Interaction with TODO 3

Erasing type arguments of a *predicate* removes precisely the type-forcing
positions tier A needs: after erasing `A` from `In`, the atom `In(x,l)` no
longer covers the guard `HasType(x, A)` *for the specific quantified `A`* (it
now only witnesses `∃A'. x:A' ∧ l : list A'`). Since atom sizes are not where
the ATP pain is (term bloat lives in constructor/function spines inside
equations), the clean resolution is:

> **Erase type arguments only of constants whose type target is not `Prop`.**
> Predicates stay fully applied; constructors and functions get erased.

If measurements later justify erasing predicate arguments too, tier A must then
use *joint covers* (`In(x,l)` + retained `T(l, list A)` together force `x : A`)
— implementable, but not worth the complexity up front. Note the reverse
direction is harmless: guards dropped by tier A never served as covers for
type-argument erasure (erasure covers are argument *positions in the same
application*, not guard atoms).

Interaction with TODO 7 (per-constructor split match axioms, see
`notes/extraction.md`): splitting removes the mandatory scrutinee guards
entirely (no exhaustiveness claim per equation), which is *complementary* — it
shrinks the population of guards that tier A/B must keep. The pattern-equation
form `∀y m. add(S(y), m) = S(add(y,m))` has no naked variables on either side
(both sides are proper applications), so under tier B its variables need no
guards, consistent with extraction.md §2.3's lambda-lifting analogy.

---

## 5. Design

### 5.1 Architecture: a post-processing pass

Implement both optimizations as one pass over the generated `fol` formulas,
applied per axiom in `translate` (coq_transl.ml:1129) before `Axhash` caching
(so caching stays coherent), and to the goal formula with the goal-specific
policy of §5.5. At that point formulas are still `App`-spines over original
constant names with uniform `App(App(Const "$HasType", t), τ)` guard nodes —
before `tptp_out`'s T-specialization/arity/predicate optimizations, which then
benefit from the smaller formulas. New module, e.g. `src/plugin/coq_guards.ml`
(add to `_CoqProject.plugin`, `hammer_plugin.mlpack`, dune).

Why not do it during translation (inside `prop_to_formula`/`convert`)? The
criterion needs the *whole* body (look-ahead for covering atoms) and a fixpoint
over guard-covers-guard; a separate pass on the finished formula is simpler,
independently testable, and keeps `coq_transl.ml` untouched except for the call
site.

### 5.2 Guard-omission algorithm (tier A; tier B as a variant)

Per formula, with a polarity flag (axioms start positive; `_HAMMER_GOAL` starts
negative — i.e. "asserted" vs "to prove"):

1. **Collect candidate guards**: positive-polarity implication guards
   `∀x. HasType(x,τ) → φ` (obligations at use sites). Leave
   negative-polarity guards and ∃-conjunct guards alone by default (they are
   facts; dropping them is `M`-safe when covered but syntactically lossy —
   revisit with the completion axioms of §5.6, or measure a variant that drops
   them too).
2. **Forced-type tables**: for each constant head `c` occurring in a hypothesis
   atom, compute once (memoized) from `Defhash`:
   `Coq_typing.destruct_type (coqdef_type (Defhash.find c))`, giving per-position
   expected types as CIC₀ terms with earlier-argument dependencies. Prop-valued
   heads (`Coq_typing.check_type_target_is_prop`) yield strict predicate atoms;
   rigid inductive type formers yield strict `$HasType` atoms. V1 restricts
   forced-type patterns to: a sort; a variable (dependency on an earlier
   argument — substitute the actual earlier argument term); a rigid application
   of an inductive/non-reducible constant to such patterns. Everything else
   (products — which the translation lifts to `$_type_N` anyway —, redexes,
   match/fix-headed) is not a cover in v1.
3. **Match**: guard `HasType(Var x, τ)` is covered by hypothesis atom
   `c t₁ … tₖ` at position `j` if `tⱼ = Var x` and the instantiated forced type
   of position `j` is syntactically equal to `τ` (both are post-translation
   terms; the translation's hash-consing of lifted types makes syntactic
   comparison meaningful, and v1's rigid-pattern restriction avoids conversion
   issues). Hypothesis position = the `JV` recursion of §3.3 implemented
   directly on the `fol` syntax (`=>`/`&`/`|`/`~`/`<=>`/`!`/`?` nodes).
4. **Fixpoint** for guard-covers-guard (§3.3, ordering discipline).
5. **Rewrite**: delete covered guard implications (and the now-vacuous
   `∀x` stays — the quantifier itself is kept; FOL quantification over the
   whole domain is exactly the semantics the criterion validated).

Tier B (separate option level) replaces step 1's "covered" test by the
undercover analysis: keep a guard iff its variable occurs naked in a positive
equation/equivalence (or in an inversion-like disjunction) — plus everything
tier A keeps covered stays droppable. Ship behind a distinct level so eval can
compare.

### 5.3 Type-argument erasure algorithm

1. For each constant `c` in `Defhash` with non-Prop type target: compute erasable
   positions per §4.1 (type-scheme positions, rigid occurrence in a retained term
   position, `Impargs`-implicit — the implicit-status list must be exported from
   the Coq side; extend `hhdef`/`Coq_convert.to_coqdef` or add a side table
   filled in `hammer_main.ml`, since `coq_transl.ml` itself does not see Coq
   API).
2. Rewrite every `App`-spine of `c` in every formula, dropping erasable
   positions present in the spine.
3. Adjust generated axioms that quantify per-position (injectivity: drop the
   conjunct for erased positions — natural if the rewrite runs after axiom
   generation, since the conjunct `A = A'` mentions variables that no longer
   occur in the atom; simplest is to rebuild inj axioms aware of erasure, or
   post-simplify `∀A A'. cons(x,l)=cons(x',l') → … ∧ A=A' ∧ …` by dropping
   equations between variables with no other occurrence).

### 5.4 Options and plumbing

- `opt_guard_omission : int ref` — 0 off, 1 tier A, 2 tier B; exposed as
  `Set Hammer GuardOmissionLevel` (pattern: `opt.ml:195`).
- `opt_omit_type_args : bool ref` — point 2; `Set Hammer OmitTypeArgs`.
- `opt_typing_completion : bool ref` — §5.6.
- Changing any of these must clear `Axhash` (and `coqterm_hash` is unaffected);
  simplest: make the option writes call a registered `Coq_transl.cleanup`-style
  invalidation hook.
- Keep `Hammer_transl`/`hammer_transl` reflecting the options so translations
  remain inspectable.

### 5.5 Goal treatment

Tier A is an `M`-equivalence, so it *may* be applied to the goal — but the
guards it would remove there are mostly **facts** of the negated conjecture
(top-level ∀-guards), which feed the guard obligations that survive in premises.
Default: leave the goal untouched (all guards kept). Optional variant for eval:
apply tier A to the goal only at positions where the guard is an obligation in
the refutation (∃ in the goal's conclusion, guards under a goal-hypothesis ∀) —
expected to matter rarely.

### 5.6 Typehood-completion axioms (optional, unconditionally safe)

For each inductive predicate / Prop-targeted constant `p : ∀(y₁:B₁)…(yₘ:Bₘ),
Prop` actually used as a cover in the problem, optionally emit

```
∀x₁…xₘ. p(x̄) → HasType(xᵢ, Bᵢ[x̄])     (for each rigid, non-proof position i)
```

These are `M`-true by typing inversion (I3) — adding them is safe regardless of
everything else — and they restore *syntactic* recoverability of dropped guard
facts (§3.3), letting the ATP bridge from a strict hypothesis it has derived to
a guard obligation another premise still carries. They cost clauses; whether
the trade is favourable is an eval question. (They are also exactly the
"soft-typing hierarchy" atoms Mizar problems carry natively.)

### 5.7 Relation to other TODO points

- **Point 7** (split match axioms): removes the mandatory scrutinee-guard class;
  do it independently; both passes compose (split equations are guard-free
  already, and tier A/B then act on inversion axioms and statements only).
- **Point 5** (monomorphisation) multiplies instances whose guards tier A then
  prunes with *concrete* covers (`T(x, nat)` covered by `Even(x)` needs no
  polymorphism at all) — the combination should compound.
- **Point 6** (specialized guard predicates `list_nat(x)`) is orthogonal
  clutter-reduction on the guards that *remain*; `tptp_out`'s existing
  T-specialization already approximates it.

---

## 6. Correctness test suite

Patterns that must keep behaving (add as `tests/plugin` cases and/or unit tests
of the pass; each is a known unsoundness from the literature or the JAR paper):

1. **Case-scrutinee exhaustiveness** (JAR §5.6): single-constructor `Set`
   inductive, match lifted out — the scrutinee guard must survive tiers A and B
   (variable naked in `x = c0`). The FOL problem with two distinct constants
   must stay consistent.
2. **Finite-type exhaustion** (Meng–Paulson): `bool`/two-element inversion
   axioms keep their guards under A and B; check no proof of `False` from
   `bool` + `nat` axioms with both passes on.
3. **Instance confusion** (type args): a polymorphic constant with a
   result-only type argument (`nil`, or `Definition myconst (A:Type) : nat`)
   must keep it; check `nil nat ≠ nil bool`-style goals don't become provable
   (they aren't stated in CIC, but e.g. premise pairs distinguished only by the
   type argument must not collapse: `length (@nil nat) = 0` vs a `bool`
   instance).
4. **Polymorphic finiteness** (Bobot–Paskevich `isUnit`): encode
   `P : ∀A:Type, A → Prop` with axioms `∀A x. P A x → ∀y:A. y = x` and
   `∀x:U. P U x` for a singleton `U` — the `y = x` variable is naked, its guard
   must survive tier B.
5. **Funext regression** (JAR §5.6): with `ClosureGuards` off and tier B on,
   the identity-lambda lifting `∀x. f(x) = x` keeps its guard (naked RHS) —
   verify the known funext-inconsistent example no longer refutes (this would be
   an *improvement* over current default).
6. **Even/le sanity**: the §1.3 examples translate with the expected guards
   dropped, and `hammer`'s end-to-end success on `tests/plugin` does not
   regress; reconstruction rate unchanged (reconstruction reads premise *names*,
   so it is insensitive except through `atp_info`).

## 7. Evaluation plan

Use the `eval/` harness on the stdlib benchmark, same protocol as the JAR paper
(fixed premise counts, Vampire/E/Z3/CVC4, fixed time limits):

- Configurations: baseline; A; A+completion; B; A+type-args; A+B+type-args.
- Metrics: ATP success rate; reconstruction success rate (the unsoundness
  canary — a rising ATP rate with falling reconstruction rate means the pass is
  producing junk proofs); problem sizes (symbol counts — the literature's best
  predictor); per-file deltas to spot systematic regressions (e.g.
  heavy-`sig`/dependent files).
- Watch premise-selection interaction: if a configuration lets ATPs refute the
  axioms, kNN will *learn* to select the inconsistency (QED-survey warning);
  falling reconstruction on many unrelated goals is the symptom.

Expected outcome, calibrated on the literature: traditional-guards → cover-based
placement was worth tens of percent relative improvement in the Isabelle
measurements at high premise counts; CoqHammer premises are guard-heavier than
Isabelle's (every statement quantifier), so tier A alone should be a visible
win, with type-argument erasure compounding on list/algebra-heavy files. But the
JAR paper's own experience is that guard-level changes move success rates by
small-but-real amounts — measure, don't assume.

## 8. Open theoretical questions (the "prove it correct" half of TODO 3)

1. Extend the PTS paper's Theorem 75 with inductive types and the tier-A rule
   (guard sub-proof replaced by strict-atom sub-proof + typing inversion, per
   §3.3). This would upgrade tier A from "true in the intended model" to a
   constructive soundness theorem for a core translation with inductives — the
   "reasonable subset of CIC" the TODO asks for. Main lemmas needed: (i) typing
   inversion for CIC₀ (I1–I3 transcribed); (ii) strictness of the intended
   interpretations of translated inductive predicates, which for the *core*
   translation is a definition rather than a theorem.
2. Tier B soundness in the presence of `eq`-as-FOL-`=` and `$HasType`: transcribe
   Blanchette et al.'s Theorem 46 model surgery; the new ingredient is that
   "types" live in the same domain and `$HasType` must be corrected alongside.
3. Whether ∃-conjunct guards (inversion witnesses) can be dropped when covered
   *without* completion axioms ever mattering in practice — pure eval question.

## References

- Ł. Czajka, C. Kaliszyk. *Hammer for Coq: Automation for Dependent Type
  Theory.* JAR 61:423–453, 2018. §5.2 (F/G/C encodings), §5.5 (FOL
  optimizations), §5.6 (guard soundness, case-scrutinee counterexample).
- Ł. Czajka. *A Shallow Embedding of Pure Type Systems into First-Order Logic.*
  TYPES 2016 post-proceedings, LIPIcs 97, 9:1–9:39. Def. 35–50 (embedding),
  Lemma 74/Theorem 75 (proof-theoretic soundness), §6 remarks (guard omission
  conjecture, monotonicity open problem). https://drops.dagstuhl.de/
- J. C. Blanchette, S. Böhme, A. Popescu, N. Smallbone. *Encoding Monomorphic
  and Polymorphic Types.* LMCS 12(4:13), 2016. Def. 34 (inferable), Def. 40–43
  (covers, undercover variables, `g@`), Lemma 45, Thms. 38/46/79, §8 (eval).
  https://www.andreipopescu.uk/pdf/LMCS2016.pdf
- K. Claessen, A. Lillieström, N. Smallbone. *Sort It Out with Monotonicity.*
  CADE-23, LNAI 6803, 2011. Calculus 1 (naked variables), calculus 2
  (predicates as guards via false-extension policies, SAT-decided).
  https://smallbone.se/papers/sort-it-out-with-monotonicity.pdf
- Why3 sources: `src/transform/encoding_guards.ml` (production featherweight
  guards `g??`), `encoding_tags.ml`, `discriminate.ml`.
  https://gitlab.inria.fr/why3/why3
- J. Meng, L. C. Paulson. *Translating Higher-Order Clauses to First-Order
  Clauses.* JAR 40:35–60, 2008. §2.3/2.8 (unsoundness patterns, finiteness
  filtering), §3 (evaluation).
- F. Bobot, A. Paskevich. *Expressing Polymorphic Types in a Many-Sorted
  Language.* FroCoS 2011, LNCS 6989. Thm. 5 (type args sound under infinite
  domains), the `isUnit` counterexample.
- J. Blanchette, C. Kaliszyk, L. Paulson, J. Urban. *Hammering towards QED.*
  J. Formalized Reasoning 9(1), 2016. History of Sledgehammer's unsound-to-sound
  encoding migration; premise-selection-exploits-inconsistency warning.
- J. Urban. *MPTP 0.2.* JAR 37:21–43, 2006 (Mizar type relativization; top-type
  guard omission).
- P. Letouzey. PhD thesis, Université Paris-Sud, 2004. §2.2 (erasure E, type
  schemes), §3.3/3.5.1 (`Ê`, type-argument filtering "purely by typing"),
  §4.3.1–4.3.2 (argument pruning, parameter dropping), p. 140 (optimization #4
  cautionary tale). https://theses.hal.science/tel-00150912
- Rocq reference manual, *Typing rules* / *Theory of inductive definitions*
  (typing inversion facts I1–I3; product subtyping rule 5 — argument-position
  rigidity). https://rocq-prover.org/doc/master/refman/language/cic.html
- This repo: `src/plugin/coq_transl.ml`, `coq_transl_opts.ml`, `coq_typing.ml`,
  `tptp_out.ml`, `opt.ml`; `notes/extraction.md` (TODO 7/9 investigation —
  split match axioms, extraction architecture, `Ê`-as-guard-calculus reading).
