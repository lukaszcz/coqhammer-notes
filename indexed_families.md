# Full support for indexed inductive families in the shallow translation

*Design note, 2026-07-16. Sources: `src/plugin/coq_transl.ml`,
`coq_erasure.ml`, `coq_transl_opts.ml` (extraction branch, Rocq 9.2); the
CoqHammer paper (Czajka & Kaliszyk, JAR 61, 2018) and the shallow PTS
embedding paper (Czajka, TYPES 2016 post-proceedings); three commissioned
literature surveys in `notes/indexed_families/research/` (fording &
pattern-matching elimination; hammer/SMT datatype encodings; erasure &
proof-irrelevance semantics) with primary texts archived in
`notes/indexed_families/papers/`; companion notes `notes/extraction.md`,
`notes/dependent_types.md`, `notes/monomorphisation.md`. All concrete FOL
outputs below were produced with `Hammer_transl` using the plugin built from
this branch. Terminology: "junk model" = the proof-irrelevant total model
with explicit ill-typed junk elements used by the soundness paper in
`notes/extraction/`.*

## TL;DR

1. **Yes, indexed inductive families can be fully supported, and the
   principled mechanism is fording** (McBride 1999, §3.5): every constructor
   `c : ∀ā. I p̄ t̄(ā)` is treated as a constructor of a *non-indexed* family
   carrying equational premises, `c : ∀ū ā. (ū = t̄(ā)) → I p̄ ū`. Indexed
   families thereby reduce, without loss, to the fragment the extraction
   machinery already handles — parametrized inductives whose constructors
   carry propositional payloads — because **index equations are just more
   propositional payload**. Every system that elaborates dependent matching
   (Coq's `inversion`, Agda's unifier, Equations, GMM06) already performs
   this reduction internally; we perform it in the translation, shallowly,
   per occurrence.

2. **The untyped FOL target dissolves the two classical obstacles to
   fording.** (a) Telescopic index equations need heterogeneous equality in
   CIC (McBride's `≃`, whose eliminator is exactly K); untyped FOL equality
   states them directly. (b) "Green slime" (defined functions in index
   positions) makes elaboration-time unification stuck; a saturation prover
   just *keeps* the equation `0 = plus m n` and reasons with `plus`'s
   defining equations — the ATP performs specialization-by-unification as
   ordinary superposition, and can even close branches the type-theoretic
   procedure cannot. We never solve index constraints at translation time;
   we only state them.

3. **Every K/UIP obstruction in the dependent-pattern-matching literature is
   a proof-relevance obstruction and vanishes in the junk model.** Deletion
   of `x = x` is exactly K (Cockx et al.); injectivity at non-linear or
   defined indices needs UIP on the indices; singleton elimination on
   indexed families (i.e. on `eq`) *is* UIP (Gilbert–Cockx–Sozeau–Tabareau,
   POPL 2019). The junk model is proof-irrelevant, hence validates UIP, so
   the *unrestricted* rule set is sound for the translation. This is also
   precisely the existing `opt_erasure_guards` story writ large: guards-off
   erasure is junk-model-valid but not CIC-replayable without UIP
   (`dep: on`); the generalization to all indexed singletons inherits the
   same dial, and Werner (LMCS 2008) — reduce singleton eliminations *only
   when the index equation holds* — is the exact syntactic ancestor of the
   guarded variant.

4. **Status quo on this branch** (verified with `Hammer_transl` probes, §1):
   the regular path already emits index equations — but only inside
   `$HasType`-mediated declaration-level inversion axioms; per-constructor
   case equations for indexed matches are emitted *unconditionally*,
   including junk equations for statically impossible branches; a
   user-written informative match on `eq` gets **no definitional axiom at
   all** (only the six `eq_rect`-family constants are special-cased); and
   the erasure classifier refuses every indexed family
   (`coq_erasure.ml:207–210`), so refinement expansion, prop-case erasure
   and enum treatment never reach `reflect`, `eq`-matches, or indexed
   subsets. "Full support" = removing that gate by classifying the *forded*
   form, and making the index equations flow to the same places the
   non-indexed payloads already flow.

5. **Three hard constraints from the literature survey** (all with
   documented real-world soundness incidents): (i) never emit unguarded
   exhaustiveness/domain-closure — in an untyped domain it is a cardinality
   bomb (Meng–Paulson JAR 2008 §2.3), and exhaustiveness axioms are exactly
   the non-monotonic sentences that can never lose their guards (Blanchette
   et al., LMCS 2016); the junk model independently forces this since junk
   is not constructor-generated. (ii) Never emit injectivity for inductive
   *type* formers (anti-classical: Hur 2010), only for fully-applied *data*
   constructors; discrimination also only fully-applied (refutable under
   funext otherwise — Cockx JFP Counterexample 35). (iii) Index equations
   are emitted *guarded, per constructor case or per hypothesis occurrence*,
   never as unconditional facts about the family — in absurd contexts index
   equations identify things no constructor justifies (Gilbert et al.'s
   `≤bad`; Brady et al.'s "we run the risk of reducing a proof of something
   which cannot be constructed, such as 5 ≤ 4!").

6. **What this buys, concretely**: `reflect P b` (ubiquitous in
   ssreflect/mathcomp — there is an `_CoqProject.mathcomp` eval target)
   becomes a first-class enum with per-tag payloads *and* index equations;
   user-written transports and every `eq`-match erase correctly (closing the
   `cast` gap of §1.3); `le`-style inversion becomes per-occurrence instead
   of `$HasType`-mediated; statically impossible branches stop generating
   junk rewrite rules; indexed-empty instances (`vector A 0` matched at
   `S n`, `Fin 0`) refute for free from discrimination. The cost is formula
   growth, which is a measured risk (refinement expansion already tipped
   threshold-noisy stdlib cells) — hence everything lands behind a new
   compile-time option screened as its own ablation axis (§7).

## 1. Status quo: what the translation does with indexed families today

Probes (`Hammer_transl`, this branch, defaults `split_case=on`,
`prop_case_erasure=on`, `erasure_guards=off`, `refinement_types=on`,
`decl_skips=on`, `wf_recursion_eqs=on`).

### 1.1 Indexed Prop family — declaration-level inversion has the equations

```coq
Inductive levp : nat -> Prop :=
| levp_O : levp 0
| levp_SS : forall n, levp n -> levp (S n).
```

```
$_inversion_levp: ∀x. HasType(x, nat) → levp(x) →
  (x = O) ∨ (∃n. HasType(n, nat) ∧ levp(n) ∧ x = S n)
```

The index equations are all there — the classic inversion principle, which
is fording read as a theorem (research report: an inversion principle *is*
the FOL image of the forded family). Adequate, but declaration-level and
guard-relativized; usable only when the premise atoms are already in play.

### 1.2 Indexed enum (`reflect`-shaped) — everything present, but
`$HasType`-mediated

```coq
Inductive breflect (P : Prop) : bool -> Set :=
| BReflectT : P -> breflect P true
| BReflectF : ~ P -> breflect P false.
```

```
$_inversion_breflect: ∀P b X. HasType(P, Prop) →
  ((b = true) ∨ (b = false)) →
  HasType(X, breflect(P, b)) →
    (P ∧ b = true ∧ X = BReflectT(P)) ∨ (¬P ∧ b = false ∧ X = BReflectF(P))
```

Payloads *and* index equations, already correct — but mediated by a
`HasType` atom, which is exactly the encoding style the extraction branch
exists to replace with inline per-occurrence expansion (cf.
`notes/dependent_types.md` §2: "never as `HasType` atoms plus unfolding
axioms"). A binder `r : breflect P b` inside a translated formula
contributes only `HasType(r, breflect(P,b))`; the inversion content is one
resolution step away *if* the axiom was premise-selected and the prover
connects them. The typing axiom for a function over `breflect` shows the
loss: `$_typeof_breflect_to_bool` says only `result = true ∨ result =
false`, with no link between result, tag, payload and index.

### 1.3 The flagship gap — a user-written match on `eq` gets nothing

```coq
Definition cast (A B : Type) (e : A = B) (x : A) : B :=
  match e in (_ = T) return T with eq_refl => x end.
```

Output: **only** an opaque `$_typeof_cast` axiom. No definitional equation
whatsoever — `cast A A eq_refl x = x` is underivable. The reason: the
scrutinee type is Prop-sorted, `opt_prop_case_erasure` consults the
classifier, and `classify_shape` (`coq_erasure.ml:207–210`) sends every
indexed family except `Acc` to `MRegular`, so the singleton-collapse path
never fires; the emit-leaf fallback for Prop scrutinees produces nothing
definitional. Meanwhile the six transport *constants* (`eq_rect`, `eq_ind_r`,
…) are special-cased by `erase_transport_head` (`coq_transl.ml:232`) — the
same construct gets erased or ignored depending on whether the user spelled
it with a stdlib constant. This asymmetry is the clearest symptom that the
current design handles an enumeration of cases, not the construct.

### 1.4 Informative indexed matches — unconditional equations, junk included

```coq
Definition vhead (A : Type) (n : nat) (v : vec A (S n)) : A :=
  match v in vec _ m return (match m with 0 => unit | S _ => A end) with
  | vnil _ => tt | vcons _ _ a _ => a end.
```

```
$_def_vhead$vcons: ∀A n m a v. vhead(A, n, vcons(A, m, a, v)) = a
$_def_vhead$vnil:  ∀A n.      vhead(A, n, vnil(A)) = tt
```

Both equations are junk-model-sound (`vhead` is total on junk), but note:
(a) no index premise `n = m` on the `vcons` equation — harmless here, and
`compile_case`'s *lifted*-case path does emit such premises
(`constructor_index_premise`, `coq_transl.ml:1030`, used at 1181), so the
two paths are inconsistent about it; (b) the `vnil` equation is a rewrite
rule for a *statically impossible* branch (`vnil : vec A 0` vs scrutinee at
`S n`) — pure noise handed to the superposition prover.

### 1.5 Summary of the gate

`classify_shape`'s indexed refusal is deliberate and its comment is correct
*for the current machinery*: the shallow expansion "records constructor
payloads but not result-index constraints", so classifying indexed families
would be unsound-or-weak. The fix is not to weaken the gate but to make the
premise of the comment false: represent the constraints.

## 2. The design in one sentence

**Ford every constructor at classification time — its index constraints
become propositional payload — and let the existing four erasure classes,
guard generator, and case compiler treat that payload exactly as they treat
`sig`'s `P x` today, with three normalization rules for the equations and
one new decidable check (rigid index-clash) for pruning impossible
branches.**

### 2.1 The forded telescope

For an inductive `I : ∀(p̄ : P̄)(ī : Ī), s` with constructor
`c : ∀(p̄)(ā : Ā), I p̄ t̄(ā)`, and an *occurrence* `I p̄ ū` (parameters
instantiated, indices arbitrary terms), define the **forded constructor
instance**:

    args    :=  ā (types instantiated with p̄, as today)
    eqns(c) :=  u₁ = t₁(ā), …, u_m = t_m(ā)

normalized by, in order:

- **N1 (pattern solving / coalescence).** If some `t_j` is a plain
  constructor-argument variable `a_k` not solved before, substitute
  `a_k := u_j` throughout and drop the equation. This is McBride's
  simplification-by-coalescence (§3.5.1) and the mirror of forced-argument
  analysis (Brady–McBride–McKinna 2004; Equations Reloaded §4.3): equations
  for *forced* arguments are redundant. It is what makes `Acc` need no
  exception: `Acc_intro : (∀y. R y x → Acc R y) → Acc R x` has result index
  `x` = its own bound variable, so `eqns` normalizes to nothing and the
  singleton collapse is unconditional exactly as today. (The well-founded
  unfolding guardrail at `coq_transl.ml:995–1004` is orthogonal and
  unchanged.)
- **N2 (proof canonicalization).** Prop-sorted subterms of the remaining
  `t_j` are replaced by `$Proof`, as everywhere else in the translation.
  Soundness is the proof-irrelevance of the model: all proofs denote one
  canonical element and `$Proof` denotes it, so `⟦f x p⟧ = ⟦f x $Proof⟧` on
  the nose — for arbitrary junk functions `f`, not only parametric ones.
  This has three independent precedents (research report §§3–6): Letouzey's
  □ / MetaCoq's `tBox` (operational), Atkey's `!₀x = !₀y` canonical erased
  realiser (algebraic), and the set-theoretic "singleton with a canonical
  element" (Lee–Werner 2011, denotational). Werner (LMCS 2008) is the
  closest formal ancestor: his repaired singleton reduction
  `(I_rec X p ā i) ⊲ (p ε̄)` **if ū =βε ā** erases the proof, canonicalizes
  erased constructor arguments to a tag, and keeps the index equation as
  the guard — our N2 + guarded collapse is that rule with "provable in FOL"
  in place of "definitionally checked".
- **N3 (Prop-index skipping).** Equations at Prop-sorted index positions
  are dropped (their two sides are proofs; the model gives them no content).
  Existing precedent: `mk_inversion_conjs` and `constructor_index_premise`
  already skip Prop positions.

Residual equations may mention: the occurrence's index terms `ū` (arbitrary,
possibly slime), parameters, surviving constructor arguments, and `$Proof`.
Constructor arguments that survive N1 and are informative are
**∃-quantified** wherever `eqns` is used in a formula position — still
first-order, still per-occurrence, hence still within the shallow discipline
(no bridge axioms, no `HasType` mediation; the memory-note constraint).

*Remark (what fording does and does not de-specialize).* Read as a CIC
declaration, the forded family has `ū` as **non-uniform parameters**, not
uniform ones: recursive constructor arguments still occur at other
instantiations (`vcons' : ∀n. S n = m → A → vec' A n → vec' A m` uses
`vec' A n` with `n ≠ m`), making it a nested inductive in the sense of
`tree A := node : tree (A*A) → tree A`. This is deliberate and immaterial.
Parameter-vs-index is a property of constructor *conclusions*, and
elimination only confronts conclusions: since every forded constructor
returns `I p̄ ū` at the generic `ū`, case analysis needs no index
unification and each branch just receives its equations as hypotheses —
constraint discharge is pay-as-you-go, one level per match. Fording removes
*index-ness*, not *heterogeneity of recursive occurrences*; the recursive
argument at `n` is ordinary data whose own equations appear only when it is
itself analyzed. In the untyped FOL output the distinction vanishes
entirely (there are only function symbols and equations), which is why the
design uses fording as a per-constructor lens for computing `eqns`, never
as a literal re-declaration.

### 2.2 Classification of the forded form (`coq_erasure.ml`)

Drop the `has_indices && not is_acc_ind → MRegular` gate. Extend
`constructor_info` to retain the result-type index terms (`targs` is already
computed by `destruct_type_app` and currently discarded) and compute
`eqns(c)` per §2.1. Then classify with `eqns(c)` **appended to the
propositional payload**:

| Family (occurrence) | Forded view | Class |
|---|---|---|
| `eq A x y` | `eq_refl`: no args, payload `{y = x}` | `CPropSingleton` with index premise `y = x` |
| `Acc R x` | `Acc_intro`: payload ∅ after N1 | `CPropSingleton`, premise ⊤ (status quo) |
| `le n m` (stdlib, non-orthogonal) | `le_n`: `{m = n}`; `le_S`: `∃m'. {m = S m'} ∧ le n m'` | Prop inversion content (already emitted); stays non-erasable for elimination into Type (correct: fails singleton criterion) |
| `reflect P b` | `ReflectT`: `{P, b = true}`; `ReflectF`: `{¬P, b = false}` | `CEnum` with per-tag payload + index equations |
| `breflect`-like, `sumbool`-with-index | same | `CEnum` |
| `bounded n` (§1 probe: carrier + prop + index) | `Bounded`: carrier `k`, payload `{k < n', n = n'}` → N1 solves `n' := n` → `{k < n}` | `CSubset` with instantiated payload — the refinement expansion *improves* (no existential residue) |
| `vec A n`, `Fin n` | recursive carrier / multiple informative args | `CRegular` (unchanged — informative indexed data is not erasure's business; §2.4 handles its matches) |

Notes:

- **Orthogonality is not required.** Gilbert et al.'s criterion (2)
  (pairwise-orthogonal constructor index patterns) exists to make
  *elimination into Type* decidable and definitional. We are emitting
  *propositional* content into a classical target: overlapping index
  patterns just yield overlapping disjuncts, which is sound. Where
  orthogonality *does* hold (concrete detagging, Brady et al.), we get the
  branch-pruning of §2.4 as a bonus.
- **The singleton-elimination boundary is respected, not crossed.** We do
  not let `le` eliminate into Type — CIC forbids it and no goal will demand
  it. What we add for Prop-sorted indexed families is only their
  *propositional* unfolding per occurrence, which CIC proves by `inversion`
  (Cornes–Terrasse; derivable with zero axioms — Monin 2010), so
  reconstruction is never blocked on these.
- **Memoization**: the memo key must include the index-pattern shape (mask
  of N1-solved positions and the rigid skeletons of residual `t̄`), since
  classification now depends on it.
- Classification remains **presentation-sensitive by design** (checked on
  actual constructor result types): `le` vs `≤`-with-two-zeros classify
  differently, as they must (Gilbert et al.'s `≤bad`; Brady's `Compare`
  "collapsible but not concretely collapsible").

### 2.3 Occurrence expansion: guards and refinement types

The guard/realizability generator (`notes/dependent_types.md` §2) extends to
classified indexed instances:

    guard(w, I p̄ ū) :=  ⋁_c  ∃(residual informative args).
                            payload_c(w) ∧ eqns_c(ū)

- `CEnum`: `guard(r, reflect P b) = (r = tagT ∧ P ∧ b = true) ∨
  (r = tagF ∧ ¬P ∧ b = false)`. Both failure directions of the naive
  index-blind expansion are fixed: elimination is no longer too weak
  (knowing `b = true` kills the `¬P` disjunct via `$_discrim_true$false`),
  and introduction is no longer unsound (proving `reflect P true` via the
  `¬P` tag dies on `true ≠ false`). This subsumes the *declaration-level*
  `$_inversion_breflect` for expansion sites; the declaration-level axiom
  remains for opaque occurrences (same coexistence as today's `CSubset`
  decl-skips: extend `skip_refinement_decl_axioms` to classified indexed
  families once measurements justify it).
- `CSubset` with index: carrier representation as today, payload now
  including the (N1-simplified) index equations, which may mention the
  carrier.
- `CPropSingleton` (Prop occurrence in hypothesis/goal position): the
  occurrence is a proposition; its guard is the inversion disjunction —
  for `e : x = y` nothing new (eq is `opt_translate_eq`-primitive); for
  other indexed Prop singletons the premise `eqns` *is* the content.
- **Indexed-empty for free.** No `CEmpty`-at-instance analysis is needed:
  `guard(w, vec A 0)`-style occurrences at constructor-clashing indices
  expand to disjuncts whose equations (`0 = S n`, …) the prover refutes
  from discrimination axioms. The classifier's mli TODO ("future
  indexed-empty instances when the occurrence analysis can prove that no
  constructor matches") dissolves: the prover does the proving.
- **Positive-position caution (the one semantic asymmetry).** In negative
  (goal) positions the disjunction asserts exhaustiveness-relative-to-guard.
  That is exactly the sound, guarded image of domain closure (research
  report: axiom (A1) may only ever appear guard-relativized; unguarded it
  is Meng–Paulson's cardinality bomb and is false in the junk model). The
  expansion is per-occurrence and always sits under the binder's guard
  position, so this is automatic — but it is the invariant the consistency
  canaries must pin (§7).

### 2.4 Match compilation (`coq_transl.ml`)

1. **Indexed Prop singletons collapse** (the `cast` gap): in
   `compile_case`/`case_lifting`, `CPropSingleton` with residual `eqns`
   collapses the match to its unique branch,
   - guards-on (`opt_erasure_guards = true`): premised on `eqns`
     (via the existing `?premise`/`combine_premises` plumbing — this is
     `erased_case_premise` reborn one layer *above* the gate that made it
     dead code, and generalized from `eq` to every indexed proof
     singleton);
   - guards-off (current default): unconditional, valid in the junk model
     because PI ⊨ UIP (Gilbert et al. §2.2 is the precise statement that
     this equivalence is UIP), with the same reconstruction debt as today's
     transport erasure (`dep: on`, accepted).
   `erase_transport_head` remains as a shortcut, but `eq_rect`'s own
   *definition* now also translates correctly, so the special-casing stops
   being load-bearing.
2. **Index premises unified across paths**: the per-constructor definitional
   equations (the `$_def_f$c` path, §1.4) get the same
   `constructor_index_premise` treatment as the lifted-case path — under a
   sub-option, since unconditional equations are sound and premises cost
   clause size; the measured winner decides the default.
3. **Rigid-clash branch pruning** (replaces junk equations for impossible
   branches): before emitting a branch equation, unify the occurrence's
   rigid index skeleton with the constructor's — pure constructor-headed
   disagreement (`S _` vs `0`) means the branch is CIC-impossible; skip it.
   This is decidable, syntactic (Brady's concrete detagging test), and
   *conservative*: anything not rigidly clashing is kept. It is a
   translation-quality change, not a soundness need (the junk equations
   were sound); it removes noise like `$_def_vhead$vnil`.
4. **Fail-hard discipline** (branch philosophy): a genuinely malformed
   input — e.g. a constructor whose `targs` cannot be extracted, arity
   mismatch between `ū` and `Ī` — raises; it is an internal translation
   error, since everything originated from well-typed Rocq terms. No
   silent `CRegular` fallback for *structurally impossible* situations;
   `CRegular` remains only the deliberate "no erasure-specific
   simplification is justified" verdict.

### 2.5 Declaration-level axiom policy (unchanged pieces made explicit)

- **Injectivity**: data constructors only, fully applied, all arguments
  including forced ones (UIP makes the unrestricted rule sound; skipping
  N1-redundant components is an optional clutter reduction). Never for the
  inductive type former itself — `I ā = I b̄ → ā = b̄` is anti-classical
  (Hur 2010) and must stay out (it currently is out; this note makes it a
  stated invariant).
- **Discrimination**: distinct fully-applied data constructors only (Cockx
  JFP Counterexample 35: under-applied constructor discrimination is
  refutable under funext, hence unsound for our model which validates
  funext-like principles on the function fragment).
- **Inversion**: keep the existing declaration-level `$_inversion_*` (they
  already carry index equations); classified families' occurrences use the
  inline expansion; decl-skips may later drop the declaration-level copy
  for classified families, measured.
- **Acyclicity**: currently absent, stays absent in this design.
  It is the one part of the term-algebra theory that is not finitely
  axiomatizable (Kovács–Robillard–Voronkov, POPL 2017); options if ever
  needed: bounded instances, the finitely-axiomatized subterm-predicate
  conservative extension, or prover-native term-algebra rules
  (`--term_algebra_rules` in Vampire). Flagged as future work with a
  measured trigger: goals lost for want of `x ≠ S x`.

## 3. Soundness obligations (additions to the paper in `notes/extraction/`)

1. **Forded-family lemma.** In the junk model, for every inductive `I` and
   instance `I p̄ ū`:
   `⟦I p̄ ū⟧ ⊇ ⋃_c { ⟦c⟧(ā) | payload_c(ā) ∧ ⟦ū⟧ = ⟦t̄(ā)⟧ }` (introduction
   direction, needed for goal-position expansion) and, restricted to
   non-junk elements, `⊆` (inversion direction, needed for
   hypothesis-position expansion). The inversion direction is the standard
   adequacy of inductive interpretations (Aczel rule sets à la Lee–Werner);
   the introduction direction is constructor typing. Both are stated
   relative to guards — the unguarded `⊆` is false because of junk, which
   is the model-side face of TL;DR-5(i).
2. **Proof-invariance of index terms** (justifies N2): for Prop-sorted `p`,
   `⟦t[p]⟧ = ⟦t[$Proof]⟧` — immediate from the model's proof irrelevance
   and `⟦$Proof⟧` being the canonical proof element. Cite Lee–Werner
   ("Proposition types are interpreted either by the empty set or a
   singleton with a canonical element") and Atkey's `!₀x = !₀y` as the
   abstract form.
3. **UIP validity** (justifies guards-off collapse and unrestricted
   injectivity): PI ⊨ UIP; the paper already needs PI, so this is a
   corollary to record, with the Gilbert et al. §2.2 singleton analysis as
   the citation that indexed singleton elimination is *equivalent* to it —
   i.e. the guards-off/guards-on dial is exactly the UIP dial and cannot be
   finessed away.
4. **Werner's guarded rule as the syntactic counterpart** of the guards-on
   variant: `(I_rec X p ā i) ⊲ (p ε̄) if ū =βε ā` (LMCS 4(3:13) §2.5) — the
   note-worthy point being that he *needs* the index check definitionally
   (subject reduction in incoherent contexts; the unchecked non-linear
   variant even breaks Church–Rosser), whereas we only need provability,
   which is strictly weaker and is what the premise encodes.
5. **Large (Type-sorted) indices**: index equations between type-terms are
   equations between their domain interpretations (types are terms in the
   untyped encoding). The inversion direction requires: if `I p̄ U`
   inhabited by a constructor with result index `T`, then `⟦U⟧ = ⟦T⟧`. In
   CIC the constructor typing gives convertibility; the model interprets
   convertible types equally. This is already implicitly used by the
   existing inversion axioms (they quantify over type arguments and equate
   them — §1.2's `$_inversion` does it for `bool`-valued and would for
   Type-valued); the paper should make it explicit. What must *not* be
   emitted: any injectivity of type formers "to invert" such equations
   (TL;DR-5(ii)).

## 4. Coverage: what "fully" means

| CIC feature | Treatment |
|---|---|
| Non-linear indices (`I x x`) | equations `u₁ = t, u₂ = t`; no restriction (UIP available; the Cockx self-unifiability caveat is a without-K concern) |
| Defined functions in indices (green slime, `I (f x)`) | equation kept; ATP unfolds `f` by its definitional axioms; branches close or stay open by proof, not by stuck unification |
| Indices mentioning proofs (`I (f x p)`) | N2: `p ↦ $Proof`; sound by model PI; the QTT/Agda-@0 discipline is the type-theoretic shadow of this rule |
| Prop-sorted indices | N3: skipped (both sides proofs) |
| Large/Type indices | equations between type terms; §3.5 |
| Dependent index telescopes (later indices' types mention earlier) | pointwise equations, order preserved; heterogeneity is free in the untyped target (McBride's motivation for `≃` doesn't arise) |
| Indexed Prop singletons (`eq`, `JMeq`-likes) | CPropSingleton + premise; closes the `cast` gap |
| `Acc` | unchanged semantics; exception dissolves into N1 |
| Indexed enums (`reflect`, indexed `sumbool`s) | CEnum + per-tag equations |
| Indexed subsets | CSubset + equations (often improved by N1) |
| Informative indexed data (`vec`, `Fin`) | CRegular, but matches gain uniform index premises + rigid-clash pruning |
| Mutual / nested inductives | per-constructor construction unchanged (each constructor is forded independently); nothing indexed-specific |
| Indexed *co*inductives | out of scope of this note (no `Defhash` inversion machinery for them today); flagged |
| What provably cannot be "full" | induction/minimality (not first-order; premise-selected instances as today), acyclicity (schema, §2.5), decidability (with uninterpreted symbols the theory is Π₁¹ — Kovács et al. Thm 2). Same epistemic status as the rest of the translation: sound, refutationally usable, incomplete by nature. |

## 5. Relation to prior art (from the surveys — see the research reports)

The design occupies a genuinely open point in the space. HOL-based hammers
never face the problem (no indexed families; "indexed" structures arrive
pre-forded as predicates, whose `.cases` lemmas with argument equations are
just premises). SMT datatypes exclude indices structurally (closed-world
initial algebras). Lean-auto ground-monomorphizes index instances away.
Liquid Haskell does per-occurrence inversion-with-equations, but in the
checker, never in the solver. F\* is the one production system emitting
per-family inversion axioms with index equations into a (nearly) untyped
solver target — fuel-guarded and `:pattern`-triggered; its two documented
incidents (typed equality leaking through native untyped `=`, #1542; and
degenerate/empty instances interacting with rank axioms, Verus #1366) are
the concrete versions of TL;DR-5's constraints, and its matching-loop
mitigation (fuel + patterns) is unavailable to us — our analogue is that
inline per-occurrence expansion has no self-instantiating axiom to loop on,
which is an argument *for* the shallow style. The type-theory line (fording,
GMM06, Cockx, Equations) supplies the reduction and the exact accounting of
which steps our model buys us for free; the erasure line (Letouzey, Brady,
QTT, Gilbert, Werner, MetaCoq) supplies the `$Proof` semantics, the forced
argument analysis, and the guarded-reduction ancestor.

## 6. Implementation sketch

Phased, all behind a new compile-time option `opt_indexed_families` (working
name) in `coq_transl_opts.ml`, patched by `eval/rebuild-config.sh` like the
existing six:

- **Phase A — classifier** (`coq_erasure.ml`): keep `targs` in
  `constructor_info`; implement `eqns` with N1–N3; extend `ind_class` with
  index-equation data (`CPropSingleton of { index_eqs }`,
  per-tag equations in `CEnum`, `index_eqs` in `CSubset`); remove the
  `has_indices` gate; extend the memo key; delete the now-redundant `Acc`
  exemption from the gate condition (keep `is_acc_ind` only where the WF
  guardrail needs it).
- **Phase B — occurrence expansion** (`coq_transl.ml` guard generator):
  emit `eqns` conjuncts (∃-closed over residual args) in `CEnum`/`CSubset`
  guard formulas; CPropSingleton hypothesis occurrences get the inversion
  disjunction where the current code punts.
- **Phase C — match compilation**: indexed CPropSingleton collapse with
  `?premise` (guards-on) / unconditional (guards-off); uniform
  `constructor_index_premise` on the `$_def_f$c` path (sub-option);
  rigid-clash pruning of impossible branches.
- **Phase D — decl-level tuning**: extend `skip_refinement_decl_axioms` to
  classified indexed families (measured); forced-argument skipping in
  injectivity axioms (optional).
- **Tests**: extend `tests/plugin/check-extraction-transl.sh` with golden
  assertions for `cast` (definitional equation appears), `reflect`
  (per-occurrence expansion), `vhead` (no `vnil` junk equation, premise
  presence per option); extend `tests/plugin/check-consistency.sh` with
  `$false`-canaries over reflect/vec/Fin-heavy dumps — the invariant to pin
  is TL;DR-5(iii)/§2.3's guarded-exhaustiveness discipline.

Interaction with `PLAN_split_case.md` (removal of `opt_split_case_axioms` /
`generic_match`): complementary — that plan removes the legacy packaged
case; this design determines what the per-constructor equations say for
indexed scrutinees. If both proceed, land split-case first (it simplifies
the paths Phase C touches).

## 7. Evaluation plan

1. Screening grid (`eval/run-screening-grid.sh`) with
   `loo-indexed-families` as a new leave-one-out axis over the current
   winner config; corpora: the existing screening set + a
   mathcomp/ssreflect corpus (the `reflect` payoff is the headline
   hypothesis: per-occurrence reflect expansion should move mathcomp goals
   that currently require the prover to chain `$HasType` inversion).
2. Watch stdlib-regression at 256+ premises for the formula-growth failure
   mode that refinement expansion already exhibited (693→729 KB tipping
   threshold-noisy cells); if it recurs, the candidate lever is decl-skips
   extension (drop the now-redundant declaration-level inversion for
   classified families) before touching the expansion itself.
3. Consistency canaries on indexed-heavy dumps (prove-`$false` over the
   full axiom set), plus the §1 probes as golden translation checks.
4. An F\*-#1542-shaped canary, targeting the specific failure class next
   to which the riskiest reclassification (`eq` → CPropSingleton) lives:
   index-equation leakage into native equality. F\*'s funext unsoundness
   arose because its type-indexed `==` was encoded as Z3's untyped `=`,
   so an equality established at one index escaped its guard and held at
   another. Our collapse of (heterogeneous) index equality to native `=`
   is the same move, sound only by the junk-model facts of §3. The canary:
   dumps engineered so that a forded equation escaping its
   `guard`/premise, or an unconditional guards-off transport equation
   (`cast e x = x`) firing on a junk proof where branches disagree, would
   let the ATPs derive `$false` — e.g. matches on `eq` between
   observably-distinct terms under an uninhabited hypothesis, and
   guards-off dumps mixing transports at several types. The general
   canaries test aggregate consistency; this one fails loudly iff an
   equation outlives its occurrence.
5. Guards-on vs guards-off over the generalized mechanism: re-run the
   erasure-guards axis; the prior +9.1pp for guards-off should persist or
   improve (more erasures, same UIP debt), but it is now measuring a
   bigger surface — do not assume transfer.

## 8. Risks and open questions

- **Formula growth** is the only empirically observed failure mode of this
  family of changes; everything lands optioned and measured (§7.2).
- **∃-rich guards**: residual informative constructor arguments produce
  existentials in guard positions; superposition provers skolemize
  hypothesis-side ∃ harmlessly, but goal-side (negative) occurrences become
  universals — clause bloat is possible on CEnum-heavy goals. Mitigation:
  N1 usually eliminates the residue (all of `eq`, `Acc`, `reflect`,
  `bounded` above have empty residue).
- **Reconstruction**: unchanged in kind — guards-off erasures need
  `dep: on`-class tactics for truly-dependent replays (accepted trade-off,
  per the erasure-guards default decision); the new Prop-singleton
  inversions are plain `inversion`-provable (K-free — Monin), so `sauto`
  reconstruction should not regress on them.
- **Model formalization debt**: §3's five obligations, of which the
  forded-family lemma is the substantial one (the others are corollaries of
  PI or already-implicit facts made explicit). The paper's TODO 7/9
  architecture has a natural slot next to the existing refinement-expansion
  soundness section.
- **Open**: whether declaration-level inversion axioms should be dropped
  wholesale for classified families (decl-skips precedent says probably,
  measurement decides); whether the `$_def` path's index premises should
  default on or off; whether a mathcomp corpus needs its own premise-count
  calibration before it can serve as the payoff metric.

## References

Research reports (this directory):
`indexed_families/research/fording-pattern-matching-elimination.md`,
`indexed_families/research/hammer-smt-datatype-encodings.md`,
`indexed_families/research/erasure-index-representation-semantics.md`.
Archived primary texts: `indexed_families/papers/` (see its README for the
full citation table). Key primaries: McBride 1999 (thesis, §3.5, §5.2);
Goguen–McBride–McKinna 2006; Cockx–Devriese–Piessens ICFP 2014;
Cockx–Devriese JFP 2018; Sozeau–Mangin ICFP 2019;
Gilbert–Cockx–Sozeau–Tabareau POPL 2019; Werner LMCS 2008; Lee–Werner LMCS
2011; Letouzey TYPES 2002 / CiE 2008; Brady–McBride–McKinna TYPES 2003;
Atkey LICS 2018; Meng–Paulson JAR 2008; Blanchette et al. LMCS 2016;
Kovács–Robillard–Voronkov POPL 2017; F\* (POPL 2016 + `uth_smt`); Vazou et
al. ICFP 2014; Sozeau et al. POPL 2020 / JACM 2025 (MetaCoq).
