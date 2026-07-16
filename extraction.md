# Breaking up match axioms and program extraction (TODO points 7 and 9)

*Investigation notes, 2026-07-05. Sources: `src/plugin/coq_transl.ml` (this repo),
the CoqHammer paper (Czajka & Kaliszyk, "Hammer for Coq: Automation for Dependent
Type Theory", JAR 61, 2018), Pierre Letouzey's PhD thesis ("Programmation
fonctionnelle certifiée — L'extraction de programmes dans l'assistant Coq",
Université Paris-Sud, 2004, HAL tel-00150912), Letouzey's "A New Extraction for
Coq" (TYPES 2002) and "Extraction in Coq: an Overview" (CiE 2008). All concrete
FOL outputs below were produced with `Hammer_transl` using the plugin built from
this branch (Rocq 9.1).*

## TL;DR

1. **Yes, breaking up match axioms per constructor should improve the ATP success
   rate**, most clearly on equational goals about defined functions. The current
   single guarded-disjunction-of-existentially-quantified-conjunctions axiom
   clausifies into many long non-Horn clauses with Skolem functions; the split
   form yields unit or near-unit equations that superposition provers (Vampire,
   E) exploit directly by demodulation/rewriting, and SMT solvers turn into
   well-behaved conditional rewrite rules. It also *removes* the one place where
   type guards provably cannot be omitted, making the translation *more* sound,
   not less. Nothing is lost logically: exhaustiveness is already provided
   independently by the per-inductive `$_inversion_*` axioms. The main risk is
   losing the "packaged case split" that ATPs sometimes exploit for inversion
   (TODO point 4); this is mitigated by the inversion axioms and can be resolved
   empirically with the `eval/` harness.

2. **Yes, this can be generalized and unified with Letouzey's extraction.** The
   per-constructor equations of point 7 are exactly the defining equations of
   the *extracted program*: `F (cᵢ x⃗) = sᵢ` is the equational reading of
   ι-reduction, i.e. of the ML `match` produced by extraction. Pushed to its
   conclusion, the translation of the *definitional* content of a Coq constant
   `c := t : τ` factors into (a) **program extraction**: emit the defining
   equations of `E(t)` (Letouzey's erasure function) as FOL axioms, and (b)
   **specification extraction**: emit the statement "`c` realizes `τ`", which is
   precisely Letouzey's simulation/realizability predicate `⟦τ⟧₂` from §2.4 of
   the thesis. The JAR paper already conjectures this factorization is worthwhile
   (§9: "It may be worthwhile to investigate if our translation could be
   factorized reusing the intermediate representation from [Letouzey's thesis]").

3. **Yes, extraction ideas fix concrete known failures**, most notably TODO
   point 9: with Letouzey's *singleton elimination* the function `h` (a match on
   a proof of a conjunction returning a `sig`) extracts to `h x y z = z`, and its
   realizability predicate gives the specification axiom
   `∀x y z. x=y ∧ y=z → x = h x y z` — both currently missing (verified below:
   today `h` gets *no* definitional axiom at all, only an opaque typing axiom).
   Extraction's logical-argument pruning and inductive-type optimizations also
   subsume or inform TODO points 2, 3, 5 and 6.

4. One important caveat discovered during the analysis: for functions defined by
   *well-founded* recursion, the extracted unfolding equations are **not** Coq
   theorems when logical preconditions are dropped (`div a 0 = S (div a 0)`
   territory), and can contradict genuine premises. Extraction survives this
   because lazy/blocked closures never unfold; an equational FOL axiomatization
   has no such protection. Specification extraction must therefore keep erased
   `Prop` premises as implication premises on definitional axioms obtained from
   `Acc`-style recursion. This is the equational analogue of exactly the
   evaluation-order problem that forced Letouzey to abandon the old "modified
   realizability" erasure (`E(λx:P. t) = E(t)`) in favour of dummy abstractions.

---

## 1. Current state: how matches are translated

### 1.1 Code

A `Case` term is lifted out by `remove_case` → `case_lifting`
(`src/plugin/coq_transl.ml`), which occurrence-lifts the expression to a symbol
`F = $_case_<ind>$<id>` applied to its informative free variables.  The
hash-consing key additionally contains the actual erased proof dependencies and
the enclosing declaration, so matches depending on different proof variables
cannot be conflated.  The `Hashing.can_aux` canonicalization of `Let` terms uses
the let body (not the binder type), which is required for this identity rule.

Informative results are compiled to one equation per constructor, recursively
flattening nested cases.  Compound scrutinees are first normalized through a
typed auxiliary `λz. match z with ...`; constructor branch arities use Rocq's
`nargs` count, so let-bound constructor declarations are not mistaken for
arguments.  Every branch is validated before the first equation is emitted.
Matches on empty Prop inductives remain unconstrained, and permitted singleton
eliminations collapse to their unique branch under the source proposition.

Proposition-valued matches use a separate specification (`G`) reading.  For a
lifted predicate `F(y⃗)` matching `t`, each constructor contributes a guarded
branch condition containing the constructor equation `t = cᵢ(...)`, its index
equalities, argument guards/premises, and the translated branch formula.  The
compiler emits both a lower and an upper bound:

```
Inh(t) ∧ ⋀ᵢ ∀x⃗ᵢ. (t = cᵢ(x⃗ᵢ) ∧ Gᵢ ∧ idxᵢ → φᵢ) → F(y⃗)
Inh(t) ∧ F(y⃗) → ⋁ᵢ ∃x⃗ᵢ. t = cᵢ(x⃗ᵢ) ∧ Gᵢ ∧ idxᵢ ∧ φᵢ
```

The inhabitation guard is load-bearing: for an empty scrutinee it makes both
bounds vacuous.  There is no `$_generic_case_*` fallback.  The two ablation
paths mean axiom omission for the occurrence-lifted symbol; unexpected shapes
raise an internal translation error.

### 1.2 Concrete outputs (verified on this branch)

`Definition mypred x := match x with 0 => 0 | S y => y end` gives (pretty-printed):

```
$_def_mypred: ∀x. nat(x) → ( (x = O ∧ mypred x = O)
                           ∨ ∃y. nat(y) ∧ x = S y ∧ mypred x = y )
```

`Nat.add` (a fix whose body is a match; the fix-lifting axiom and the case-lifting
axiom get merged by the lifting-axiom simplification of JAR §5.5):

```
$_def_Nat.add: ∀n m. nat(n) → ( (n = O ∧ add n m = m)
                              ∨ ∃y. nat(y) ∧ n = S y ∧ add n m = S (add y m) )
```

Note: guard on `n` (free variable of the matched term) but not on `m`.

A nested match `g x = match x with 0 => 0 | S y => match y with 0 => 1 | S z => z end end`
produces a single axiom with the inner disjunction nested inside the outer
existential:

```
$_def_g: ∀x. nat(x) →
  ( (x = O ∧ g x = O)
  ∨ ∃y. nat(y) ∧ (nat(y) → x = S y ∧ ( (y = O ∧ g x = S O)
                                      ∨ ∃z. nat(z) ∧ y = S z ∧ g x = z )) )
```

A non-variable scrutinee `k b = match negb b with true => 0 | false => 1 end`:

```
$_def_k: ∀b. bool(b) → ( (negb b = true  ∧ k b = O)
                       ∨ (negb b = false ∧ k b = S O) )
```

And, per TODO point 9, the function

```coq
Definition h (x y z : nat) (p : x = y /\ y = z) : {u : nat | x = u} :=
  match p with conj p1 p2 => exist (fun u => x = u) z (eq_trans p1 p2) end.
```

produces **no definitional axiom whatsoever** — only
`$_typeof_h : HasType(h, $_type_12)` where `$_type_12` unfolds to a guard saying
`∀x y z. nat(x) → nat(y) → nat(z) → (x=y ∧ y=z) → HasType(h x y z, sig nat ($_lam_15 x))`
(with `$_lam_15` axiomatized by `P(lam_15 x u) ↔ x = u`). The specification
content is technically *present* but buried inside a `HasType` atom over an
opaque `sig`-typed term that no other axiom connects to anything — unusable, as
the TODO says.

### 1.3 The soundness constraint on guards

The JAR paper (§5.6) proves the design point that matters most here: guards for
the free variables of lambda-lifted terms are omitted by default (a slight
success-rate win, conjectured sound modulo the `eq`-to-`=` issue), but guards for
the free variables of the *matched term* **cannot** be omitted. With
`I(c : Set := c0 : c)` the guardless axiom for `case(x, c, 0, c, c0)` would be
`∀x. x = c0 ∧ F x = c0`, which is inconsistent the moment two provably distinct
constants exist. The inconsistency comes from the **exhaustiveness claim** of the
disjunction: it asserts that *every* element of the (untyped) FOL domain is of
constructor form. That claim is simply false for "junk" domain elements, so it
must be relativized by the guard.

This is the deep reason why point 7 is attractive: the per-constructor equations
make no exhaustiveness claim at all, so the problematic guard becomes
unnecessary rather than merely omittable (see §2.3).

### 1.4 Interaction with reconstruction (TODO point 4)

`provers.ml:39-56` parses the ATP proof and collects the used axioms whose names
begin with `$_case_` and `$_inversion_` into `atp_info.cases` /
`atp_info.inversions`; `hammer_main.ml:291` unions both lists and feeds them to
the reconstruction tactics. So ATPs demonstrably *do* use match axioms, sometimes
for inversion (the disjunction gives a free case split on the scrutinee). Any
change to the match axioms must preserve (or improve) the quality of this signal;
splitting actually improves it, because per-constructor axiom names can record
*which branch* was used (§2.6).

---

## 2. Point 7: one axiom per constructor

### 2.1 The proposal, precisely

For a case-lifted `F` over variables `y⃗` matching on term `t` of inductive type
`I p⃗` with constructors `cᵢ : ∀p⃗. ∀x⃗ᵢ. I p⃗`:

- **Variable scrutinee** (`t = x`, `x ∈ y⃗`): emit for each `i`
  `∀ y⃗∖{x}, x⃗ᵢ. [guards?] F y⃗[cᵢ p⃗ x⃗ᵢ / x] ≈ C(sᵢ x⃗ᵢ)` — substitute the
  constructor pattern for `x`, as in the TODO example
  `F O = t1'`, `∀y. nat(y) → F (S y) = t2'`.
- **Compound scrutinee** (e.g. `negb b`): substitution is impossible; emit
  conditional equations
  `∀ y⃗, x⃗ᵢ. t = cᵢ p⃗ x⃗ᵢ → F y⃗ ≈ sᵢ`, i.e. for `k`:
  `∀b. negb b = true → k b = O` and `∀b. negb b = false → k b = S O`.
- **Nested matches**: recurse, i.e. compile the tree of matches into a flat set
  of pattern equations, exactly like ML pattern-match compilation. For `g` above:
  `g O = O`, `g (S O) = S O`, `∀z. g (S (S z)) = z`. This eliminates the
  disjunction-under-existential nesting entirely.
- **Fixpoints**: composed with the existing lifting-axiom merge (JAR §5.5), a
  structural fix-with-match becomes literally the recursive program:
  `∀m. add O m = m` and `∀y m. add (S y) m = S (add y m)`. (The merge
  optimization currently rewrites a single axiom `∀x⃗.φ(F x⃗ = G x⃗)`; it needs a
  small generalization to distribute over a *list* of axioms for `G`.)

### 2.2 Logical strength: nothing is lost

The two formulations are inter-derivable *given axioms that are already emitted*:

- split ⊢ old: from `$_inversion_I` (verified present, e.g.
  `$_inversion_nat: ∀X. nat(X) → X = O ∨ ∃y. nat(y) ∧ X = S y`), case-split on
  the scrutinee's guard and rewrite with the matching equation. One extra
  resolution step versus using the old axiom directly.
- old ⊢ split: instantiate the scrutinee to `cᵢ x⃗ᵢ` and discharge the wrong
  disjuncts using the `$_discrim_*` axioms (also already emitted).

So the choice is purely about *proof-search pragmatics*, with one caveat: the
inversion axiom is guarded by `HasType`, so an ATP wanting to case-split on a
compound scrutinee `t` must first derive `HasType(t, I)` from the typing axioms.
That derivation is available (`$_typeof_*` axioms) but costs inferences; this is
the one scenario where the old packaged form can be strictly cheaper (see risk
analysis, §2.5).

### 2.3 Soundness: the split form is *better*

Intended-model argument: interpret the FOL domain as closed CIC terms up to
conversion (the model sketched for the core translation soundness proof). The
per-constructor equations with distinct constructor patterns form an orthogonal
rewrite system; `F` can be interpreted as the case function extended arbitrarily
outside constructor-formed arguments. Each equation is then *true for all domain
elements*, junk included — e.g. `∀b. negb b = true → k b = O` holds vacuously for
junk `b` since `negb b` is then a stuck term distinct from `true`. In contrast
the disjunctive axiom is false at junk points, which is exactly why its guard is
mandatory. Consequences:

- The mandatory guards on `fvars(matched_term)` disappear (they currently
  pollute every case and every fix-with-match definition, cf. `nat(n)` in
  `$_def_Nat.add`).
- The guard on the fresh constructor-argument variables (`nat(y)` in the TODO's
  axiom 2) has the same status as guards on lambda-bound variables in
  lambda-lifting, and per the TODO should be treated uniformly with them: omit
  it when `opt_closure_guards` is false (the default configuration, with the
  same "conjecturally sound modulo `eq`-translation" caveat as JAR §5.6), and
  generate it when `opt_closure_guards` is true — where it comes out
  automatically from the `close`/`make_guarded_forall` machinery rather than
  needing a special case. Either way, `y` must not inherit the special
  mandatory-guard treatment that matched-term free variables get today; that
  requirement disappears with the disjunction (§1.3).

### 2.4 Clause-shape analysis: why ATPs should do better

CNF of the current `mypred` axiom (Skolem `f` for the existential):

```
¬nat(x) ∨ x = O            ∨ x = S(f(x))
¬nat(x) ∨ x = O            ∨ nat(f(x))
¬nat(x) ∨ x = O            ∨ F(x) = f(x)
¬nat(x) ∨ F(x) = O         ∨ x = S(f(x))
¬nat(x) ∨ F(x) = O         ∨ nat(f(x))
¬nat(x) ∨ F(x) = O         ∨ F(x) = f(x)
```

Six 3-literal non-Horn clauses, two positive-equality literals per clause, a
Skolem function, and `F`'s value expressed only via the Skolem term. Nested
matches multiply this combinatorially (the `g` axiom clausifies into dozens of
clauses). Superposition provers handle such clauses, but they cannot *orient*
them; every use requires case-splitting search.

The split form for `mypred`:

```
F(O) = O                      (unit equation)
F(S(y)) = y                   (unit equation; guard omitted per §2.3)
```

Unit equations are orientable rewrite rules: E and Vampire use them for
demodulation and rewriting during simplification, essentially evaluating the
function inside the proof search at unit cost, with no case splits and no Skolem
functions. For SMT solvers (CVC4, Z3 — both run by `provers.ml`), conditional
equations with constructor patterns are ideal trigger/E-matching material. This
mirrors how the successful HOL hammers work: Sledgehammer never sees a
disjunctive "definition of `+`" — it exports the per-constructor simp rules
(`add 0 m = m`, `add (Suc n) m = Suc (add n m)`) because in HOL those *are* the
definitional theorems. Point 7 recovers for CoqHammer what HOL hammers get for
free, and it is well established there that defining equations are among the
most useful premises. It is also consistent with this repo's own experience that
ordering-oriented equational reasoning works (TODO point 8, `hhlpo.ml`, rewriting
actions in `sauto.ml`).

A secondary benefit: the axioms shrink. The `guards_{fvars(t)}` prefix
disappears, existentials disappear, and nested matches flatten. Since premise
selection operates at the level of Coq constants (whole `Axhash` entries), not
individual FOL axioms, splitting does not fragment the premise-selection ranking;
it only changes what the ATP receives for each selected constant.

### 2.5 Risks and mitigations

1. **Loss of the packaged case split** (relevant to TODO point 4): today an ATP
   that knows `nat(n)` gets "either `n = O` and `F n = t₁`, or `n = S y` and
   `F n = …`" in one clause set, effectively doing inversion on the scrutinee.
   After splitting it must chain `$_typeof` → `$_inversion_I` → equations. For
   *variable* scrutinees appearing in the goal this is usually fine (the
   inversion axiom is selected whenever the type is relevant); for compound
   scrutinees under several quantifiers it may occasionally cost a proof.
   Mitigation: the compiler records matched inductives per enclosing
   declaration, and `get_axioms` **delivers** their inversion, injectivity,
   discrimination and constructor axioms whenever the declaration is selected.
   Proposition-valued bounds carry constructor exhaustiveness internally.
2. **More axioms per match** (k instead of 1). Harmless for clause count (the
   old axiom clausifies to ≥ 3k literals anyway) but each new axiom gets a name;
   `get_cases` in `provers.ml` must be taught the new naming scheme.
3. **Interaction with `opt_simpl`/lifting-axiom merging** as noted in §2.1 — a
   mechanical generalization.
4. **Proposition-valued branches** use the lower/upper `G` bounds above.
   Empty and indexed-singleton canaries pin the inhabitation and index premises.

### 2.6 Reconstruction signal improves

Name the split axioms `$_case_<ind>$<id>$<constructor>`. Then `atp_info.cases`
reveals not only *which* match the ATP used but *which branches*, which is
strictly more information for the `inv:`/`cases:`-style options of the
reconstruction tactics (TODO point 4's "make some intelligent use of other
information in atp_info"). `get_cases`/`get_inversions` keep working with a
one-line change to name parsing.

### 2.7 Implementation sketch and evaluation

- Add `opt_case_split_axioms` to `coq_transl_opts.ml`. Note all options there
  except `opt_closure_guards` are compile-time constants; consider making this
  one (and eventually others) runtime-settable so `tacbest.ml`-style strategy
  search or the parallel GSMode strategies can vary the translation per ATP —
  Vampire/E may prefer split equations while some strategy keeps the packaged
  disjunction.
- Implement in `case_lifting`: instead of one `add_inversion_axioms0` call,
  iterate over constructors; substitute patterns for variable scrutinees,
  premise form otherwise; recurse into branch-level `Case` nodes (flattening);
  guard policy per §2.3.
- Generalize the lifting-axiom merge to lists of defining axioms.
- Update `provers.ml` name parsing.
- A/B on the `eval/` benchmark harness (stdlib), comparing success rate overall
  and on the equational subsets; also watch reconstruction rate, since
  reconstruction re-proves from premises and is insensitive to the FOL axiom
  shape except through `atp_info`.

Expected outcome: measurable win on goals whose proofs need computing with
defined functions (arith, lists); neutral-to-slightly-negative on pure
inversion-style goals, recoverable via mitigation 1. Given how central
`$_def_*` axioms of recursive functions are to stdlib proofs, my expectation is
a net improvement of a few percentage points, but this must be measured — the
JAR paper's own experience (§5.6) is that guard-level changes move success rates
by small but real amounts.

---

## 3. What is actually in Letouzey's thesis (relevant parts)

For reference, the thesis (French, 229 pp; English translation exists as
`these_letouzey_English.ps.gz` on his page — the PDF there has Type-3 fonts and
does not yield text, the HAL French PDF does) develops:

- **§2.2, Définition 9 — the erasure function `E`**, from Cic to an *untyped*
  `Cic₂` with an extra constant `□` ("2" in the thesis): any subterm that is a
  type scheme or whose sort is `Prop` becomes `□`; otherwise `E` is structural
  (`E(case(e, P, f⃗)) = case(E(e), □, E(f⃗))`; lambdas keep a *dummy binder*
  `λx:□`). Crucially `E` is a pure *pruning*: no structural change. The old
  extraction's rule `E(λx:P. t) = E(t)` for `P : Prop` ("modified
  realizability") is rejected because under strict (OCaml) evaluation dropping
  logical abstractions changes evaluation order: `(E(f) 0)` would compute where
  Coq's `(f 0)` is a blocked closure waiting for a proof of `0≠0` — leading to
  `False_rec` exceptions or non-termination (`Acc_rec`) (§2.1). The dummy
  abstractions are later removed by a separate optimization with η-protection
  at partial-application sites (§4.3.1): total applications drop the `□`
  argument, partial applications become `fun _ → …`.
- **§2.3 — syntactic correctness**: extracted-term reduction simulates source
  reduction (with ad-hoc rules `(□ u) → □` and singleton-case reduction);
  strong normalization in a restricted system, weak reduction in full Cic;
  weak normal forms agree.
- **§2.4 — semantic correctness via simulation predicates** (the part relevant
  to *specification extraction*, see §5): a family of predicates `T̂ : T → Λ →
  Prop` ("`t` is correctly extracted by the untyped term `p`"), generated by a
  transformation `⟦·⟧` with the key clause
  `⟦∀x:T. T'⟧₂ f p = ∀x ∀x'. ⟦T⟧₂ x x' → ⟦T'⟧₂ (f x) (p x')`, trivial predicate
  (`True`) for `Prop`, and for each inductive `I` an inductively defined
  simulation predicate `Î` relating `I`-values to their extractions
  constructor-wise. Realizability is derived: `p r T ⇔ ∃t:T. t ∼_T p`, and the
  main theorem is `t ∼_T E(t)`. The worked example (§2.4.4) is Euclidean
  division `div : ∀a b, b≠0 → {q | q*b ≤ a ∧ a < (S q)*b}`, whose simulation
  predicate collapses (since the `Prop` components are trivial) to: for
  arguments simulating naturals `a`, `b` and *any* third argument, the result is
  `exist_Λ q'` with `n̂at q q'` and `P a b q` — i.e. exactly the pre/post
  specification of the extracted program.
- **§2.6 — refinements**: matches on *empty* inductives are dead code
  (replaceable by anything; `assert false` in OCaml) — independent of the
  logical/informative status; **singleton elimination** (§2.6.2): matches on
  logical singletons (`eq`/`eq_rec`, `and`-like single-constructor `Prop`s,
  `Acc_rec`) reduce as `case_n(□, P, f) → f □ … □` and can all be pre-compiled
  away at extraction time (Théorèmes 10–11 justify doing this reduction
  *strongly*, under binders); `(□ u) → □` handling per target language (OCaml
  needs the argument-absorbing fixpoint `let rec f _ = f`, Haskell's laziness
  never evaluates it) (§2.6.3); fixpoint guard semantics vs. ML recursion
  (§2.6.4).
- **Ch. 3 — typing of extracted terms**: extracted code is in general not
  ML-typable (dependent types, `nArrow`-style variable arity, `strange` /
  absurd-context type casts §3.1.6); rather than restrict, insert `Obj.magic` /
  `unsafeCoerce` automatically via a type-inference pass (algorithm M variant);
  **`Ê` type extraction** (§3.3.5): `Prop`-sorted types ↦ `□`, sorts ↦ `□`,
  `∀x:A.B ↦ Ê(A) → Ê(B)` (or `□` if `Ê(B) = □`), inductive/type-constant heads
  applied to extracted arguments, and an *unknown-type* approximation `⊤` for
  everything not expressible (case/fix/free-variable heads). `Obj.magic` is
  semantically the identity, so correctness (Ch. 2) is unaffected.
- **§4.3 — implementation optimizations**: pruning of logical/`□` arguments of
  functions *and constructors* (inductive parameters are always dropped from
  constructor types; remaining `□` constructor arguments dropped); **informative
  singleton unboxing** (`sig A P` extracts to just `A`; `exist t` to `t`; its
  match to a `let`) — with the side condition that the single remaining
  argument's type must not mention the inductive itself; records to native ML
  records with dot projections; controlled inlining/unfolding (§4.3.3);
  discussion of why total proof-argument removal is only done at top-level
  argument positions (types of higher-order arguments are not rewritten).

The CiE 2008 overview confirms this architecture is what shipped in Coq 8.x and
summarizes the correctness story ("collapses (but cannot completely remove) both
logical parts and types. A complete removal would induce dangerous changes in
the evaluation of terms").

---

## 4. Point 7 *is* extraction: the precise connection

The TODO's remark "This is related to program extraction" can be made exact:

> The per-constructor axioms for a case-lifted constant `F` are precisely the
> defining equations of the ML function that Letouzey's extraction produces for
> that match, read as first-order equations. Equivalently: they are the
> equational image of the ι-reduction rules `case(cᵢ v⃗, P, f⃗) →ι fᵢ v⃗`,
> specialized to the lifted function.

`E` erases exactly the parts CoqHammer already maps to `$Proof`/drops in
`CΓ(ts)` (proof arguments) and to `$Any`/type guards (type arguments), and the
lambda/fix/case-lifting of `coq_transl.ml` is the supercombinator conversion of
the extracted program. What differs today is only the *case* clause: extraction
compiles a match to computation rules; CoqHammer axiomatizes it as an inversion
disjunction. Point 7 aligns the two. Concretely, for `Nat.add` the split
translation *is* `let rec add n m = match n with O -> m | S y -> S (add y m)`
as a rewrite system — the thing extraction outputs.

This viewpoint also answers the guard question of §2.3 conceptually: the
extracted program is a rewrite system that is *silent* off its patterns, so its
equations are true of any conservative extension — no exhaustiveness, no guard.
The inversion content (exhaustiveness) belongs to the *type*, and indeed lives
in the per-type `$_inversion_*` axioms, which are the FOL image of the datatype
declaration rather than of any program.

---

## 5. Unifying further: extraction + specification extraction as a translation architecture

The JAR paper's own suggestion (§9) is to factor the translation through
Letouzey's intermediate representation. Based on the above, the natural
architecture for the *definitional* part of the translation of `c := t : τ` is:

1. **Program extraction** (Letouzey's `E`, plus the §2.6/§4.3 refinements):
   produce an untyped functional program for `c`. Then lambda/fix/case-lift it
   (as now) and emit its defining equations per constructor (point 7). Because
   FOL axioms are consulted, not executed, the evaluation-order machinery that
   dominates Letouzey's design (dummy abstractions, `(□ u) → □`, argument
   absorption) is unnecessary — proof arguments can simply be dropped as
   `CΓ` already does. **Except** (the caveat of the TL;DR): where extraction
   relies on "this closure is never applied / this branch never runs" for
   *partial* correctness — `False_rec` dead code, and `Acc`-style well-founded
   fixpoints whose unfolding is only conditionally true — the FOL side must
   compensate, since an equation, unlike a closure, is "already applied".
   Concretely: an unfolding equation obtained through an erased logical
   precondition `P` must keep `F(P)` as a premise (recursive-realizability
   style, not modified-realizability style). Example: from the well-founded
   `div` one must emit `∀a b. b ≠ O → div a b = (if b ≤? a then S (div (a−b) b) else O)`
   and not the unconditional equation, whose instance `div a O = S (div a O)`
   contradicts a legitimately provable premise like `∀a. div a O = O`.
   The implementation now handles this by guarded WF equations; when the
   corresponding ablation is off, the occurrence-lifted symbol simply receives
   no defining equation.

2. **Specification extraction** (the TODO point 9 term): for the *type* `τ`,
   emit the realizability statement `⟦τ⟧₂ ⌜c⌝ c` — Letouzey's simulation
   predicate applied to the constant, with the FOL constant `c` playing the role
   of its own extraction. Unfolding `⟦·⟧₂`:
   - informative `∀x:T` gives `∀x. guard → …` — exactly the current `G`
     function's clause; the guard atom `HasType(x, T)` is the FOL proxy for
     `⟦T⟧₂`;
   - `Prop` premises give `F(P) → …` — exactly the current `type_to_guard`
     clause;
   - but at *inductive result types carrying `Prop` content* it gives what `G`
     today cannot: the constructor-wise simulation predicate `Î`, i.e. an
     inversion axiom *enriched with the propositional payload*. For `sig A P`,
     `ŝig` says the value is of the form `exist x h` with `A(x)` **and `P x`**;
     after informative-singleton unboxing this collapses to
     `HasType(c…, A) ∧ P (c…)`.

   Worked example (point 9's `h`): step 1 gives, via singleton elimination
   (match on the logical singleton `and`), constructor-argument pruning and
   `sig`-unboxing, `E(h) = λx y z _. z`, hence the definitional axiom
   `∀x y z. h x y z = z`. Step 2 gives
   `∀x y z. nat(x) → nat(y) → nat(z) → (x = y ∧ y = z) → x = h x y z`
   (the `sig` layer contributing `HasType(h x y z, nat)` and the predicate
   `x = h x y z`). These are precisely the two axioms the TODO asks for. Note
   they are *both* needed in general: the definition may be `Prop`-blind
   (`h = z`) while the spec carries the logical content, and conversely for
   underspecified functions (`div` with junk at `b = 0`) only the spec is
   usable.

   Two further payoffs of doing specification extraction through `⟦·⟧`:
   - The current inversion axioms (`mk_inversion`, `mk_prop_inversion`) are the
     degenerate `Prop`-content-free shadow of `Î`; `opt_precise_inversion` is a
     step toward `Î`. Deriving them uniformly from `⟦·⟧` would also fix the
     "pair used as conjunction" problem (JAR §9): `⟦·⟧` computes the predicate
     per *instance*, so `prod A B` with propositional `A` gets its `A`-component
     interpreted as a formula rather than a guarded term — the four-variants
     problem disappears because the variants are just different unfoldings of
     the same transformation.
   - Soundness. The intended model for the core translation becomes crisp: the
     domain is extracted terms, `HasType(x, T)` is interpreted as realizability
     `∃t:T. t ∼_T x`, and the correctness theorem `t ∼_T E(t)` of thesis §2.4.8
     is exactly the statement that the emitted axioms hold in the model. A
     soundness proof of the improved translation could be structured as a
     corollary of Letouzey's Théorème (validity of `⟦·⟧`, §2.4.7) rather than
     built from scratch.

3. **Type extraction `Ê` as the guard calculus** (TODO points 3, 5, 6): `Ê`
   answers "which types survive erasure and in what shape" — `Prop` and sorts
   become `□` (no guard), unknown/dependent positions become `⊤` (= `$Any`, no
   informative guard possible), and type constructors survive applied to
   extracted arguments — which is exactly the `cᵀ(t₁,…,tₙ, y)` guard
   optimization of JAR §5.5 and the proposed `list_nat(x)` specialization of
   TODO point 6. TODO point 3 (omit guards inferable from context) is, in this
   reading, "the guard is redundant where ML type inference would reconstruct
   the type of the extracted variable" — Letouzey's Ch. 3 type-checker
   (algorithm M with `Obj.magic` insertion) is a ready-made blueprint for a
   redundant-guard analysis: guards are needed precisely at (the FOL analogue
   of) `Obj.magic` positions, i.e. where the approximation loses information.
   TODO point 2 (omit implicit/parameter arguments to constructors) is §4.3.2
   verbatim: inductive parameters never carry computational content and are
   *always* dropped from constructors by extraction; the thesis proves this
   safe. (For the hammer, dropped constructor parameters must remain recoverable
   for reconstruction — but reconstruction works from the Coq premises, not the
   FOL terms, so this is only a naming/mapping concern.)

4. **What does *not* transfer**: `Obj.magic`/typing of the target (FOL is
   untyped — this entire chapter of difficulties evaporates, which is an
   argument that the hammer's target is *easier* than extraction's);
   module/functor extraction (Ch. 4.1) — the hammer sees a fully elaborated
   environment; code-efficiency optimizations like tail recursion or record
   dot-access.

### Suggested incremental path

1. Implement point 7 (per-constructor case axioms) directly in `case_lifting`
   — self-contained, no new intermediate representation needed — and benchmark
   with `eval/`. This is the highest value-to-effort step and validates the
   "extraction as rewrite system" reading empirically.
2. Add singleton elimination for matches on logical singletons (`eq_rec`-,
   `and`-, `Acc`-style single-constructor `Prop`s with non-informative
   arguments) in `case_lifting`/`convert`: instead of `generic_match`, translate
   `case(p, P, f)` to `C(f □ … □)`. This alone unblocks the "small
   propositional inductive types" class (JAR §9) and most of point 9's
   definitional half — with the well-founded-recursion premise caveat wired in
   from the start (`Acc_rec`: keep the erased `Acc`/precondition premises as
   guards on the emitted equations, or initially just keep `Acc_rec`
   applications as `generic_match` and only handle the `eq`/`and`/`sig` cases).
3. Implement specification extraction: replace `make_guard`'s opaque
   `HasType(u, I p⃗)` for `Prop`-carrying inductives (`sig`, `sigT`, `sumbool`,
   `exists`-in-`Set`, records with proof fields) by the unfolded `Î` predicate
   (inversion-with-payload), starting with the informative-singleton special
   case where it collapses to a conjunction. This is point 9's specification
   half and directly subsumes `opt_precise_inversion`.
4. Longer term: introduce the explicit `Cic₂`-style intermediate layer (the JAR
   §9 suggestion) so that erasure decisions (`check_prop`, proof-variable
   tracking, `□`) happen once, before lifting, instead of being re-derived
   locally throughout `convert`/`case_lifting`/`make_guard` — and revisit
   points 2/3/5/6 as `Ê`-driven guard optimizations on top.

---

## 6. Answers to the three questions

**Would per-constructor match axioms improve the success rate?** Very likely
yes, for the clause-shape reasons of §2.4 (unit rewrite rules vs. non-Horn
disjunctions with Skolems), with the strongest gains on equational/computational
goals; the design removes a mandatory guard class and is sound by a term-model
argument (§2.3). The identified risk (packaged inversion, §2.5) is bounded and
measurable; the `eval/` harness should arbitrate. No logical strength is lost
(§2.2).

**Can it be generalized/unified with Letouzey's extraction?** Yes — point 7 is
the case clause of "translate the extracted program as a rewrite system" (§4).
The full generalization is the two-component architecture of §5: program
extraction (`E` + §2.6/§4.3 refinements) for definitions, specification
extraction (`⟦·⟧₂` simulation predicates) for types. The JAR paper already
gestures at exactly this factorization.

**Could extraction ideas improve the translation?** Yes, concretely: singleton
elimination fixes the small-propositional-inductive-types limitation and point
9's missing definitions; `Î`-style enriched inversion fixes point 9's missing
specifications and the `pair`-as-conjunction issue; constructor-parameter
pruning is point 2 with a correctness proof already on the shelf; `Ê` is a
blueprint for guard optimization/monomorphization (points 3, 5, 6); and the
realizability semantics offers a soundness framework for all of it. The one
place where the hammer must be *more* conservative than extraction is erased
logical preconditions on well-founded recursion, where lazy non-execution
protects extraction but nothing protects an equational axiomatization (§5.1).

## References

- Ł. Czajka, C. Kaliszyk. *Hammer for Coq: Automation for Dependent Type
  Theory.* J. Autom. Reasoning 61:423–453, 2018. §5 (translation), §5.6
  (guard soundness), §9 (limitations; the factorization suggestion).
  https://doi.org/10.1007/s10817-018-9458-4
- P. Letouzey. *Programmation fonctionnelle certifiée — L'extraction de
  programmes dans l'assistant Coq.* PhD thesis, Université Paris-Sud, 2004.
  HAL: https://theses.hal.science/tel-00150912 (French PDF; English:
  https://www.irif.fr/~letouzey/download/these_letouzey_English.ps.gz).
  Key sections: 2.1–2.2 (E), 2.4 (simulation predicates; div example 2.4.4),
  2.6 (empty inductives, singleton elimination), 3.1.6/3.2/3.3 (typing, Ê,
  Obj.magic), 4.3 (logical-argument and inductive optimizations).
- P. Letouzey. *A New Extraction for Coq.* TYPES 2002, LNCS 2646.
  https://www.irif.fr/~letouzey/download/extraction2002.pdf
- P. Letouzey. *Extraction in Coq: an Overview.* CiE 2008, LNCS 5028.
  https://www.irif.fr/~letouzey/download/letouzey_extr_cie08.pdf
- CoqHammer documentation: https://coqhammer.github.io/ (translation options,
  `sauto` `inv:`/`ctrs:`/`cases:` options, stated limitations).
- This repo: `src/plugin/coq_transl.ml` (`case_lifting`,
  `add_inversion_axioms0`, `mk_inversion`, `mk_guards`),
  `src/plugin/coq_transl_opts.ml`, `src/plugin/provers.ml` (`atp_info`),
  `TODO.md` points 2–9.
