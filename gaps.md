# Remaining coverage gaps of the extraction translation, and how to close them

*Gap inventory, 2026-07-16. Written as the follow-up question to
`notes/indexed_families.md`: assuming fording-based full indexed-family
support, what does the extraction translation still not fully support that it
could? Sources: `src/plugin/coq_transl.ml`, `coq_transl_opts.ml`, `tptp_out.ml`
(extraction branch, Rocq 9.1); the JAR 2018 CoqHammer paper (esp. §9, known
limitations) and the TYPES 2016 shallow PTS embedding paper; sibling notes
`notes/monomorphisation.md` (TODO 5/6), `notes/dependent_types.md` (TODO 9),
`notes/extraction.md` (TODO 7/9), `notes/indexed_families.md` and its research
reports in `notes/indexed_families/research/` (cited below as [R-ford],
[R-enc], [R-eras]). Tactic-level claims about `congruence`/`sauto`/`lia`
were verified on this branch (probe: `n <> S n`).*

## TL;DR

After indexed families, nothing in CIC's *term and type language* remains
structurally unsupported. The residual gaps are of three kinds, in
priority order:

1. **One designed-but-unbuilt transformation**: heuristic monomorphisation +
   type-guard fusion (§1) — the largest expected win, design complete in
   `notes/monomorphisation.md`.
2. **Two principled extensions of what the ATPs are asked to do**:
   induction instances / induction-capable backends (§2), and typed backends
   with native arithmetic for Rocq's numeric types and primitives (§3);
   plus higher-order backends (§4).
3. **Finite remainders with known shapes**: coinductives/corecursion (§5),
   term-algebra acyclicity (§6), and Letouzey-style signature pruning (§7).

Suggested sequencing: §1 → §3 (it reuses §1's typed-output groundwork) → §2
(orthogonal, high value, cheap first increment) → §7 (cheap, clause-size
savings compound with everything) → §6 (optioned, trigger-driven) → §4, §5
(as corpus demand appears). Every item lands behind a compile-time option
and gets a screening axis, per the eval methodology already in place.

---

## 1. Polymorphism: monomorphisation and type-guard fusion (TODO 5/6)

**Status**: fully designed (`notes/monomorphisation.md`), unimplemented.
This entry exists for completeness of the inventory; see the design note.

**Gap.** Polymorphic constants are translated once, generically, with
type-variable guards and types-as-terms. Consequences (JAR §9): higher-order
applications never become atoms (`P @ x` instead of `lt(O, x)` — kills e.g.
`List.Forall` goals), one generic `prod` where instances differ in
Prop-ness ("four definitions of pair"), and pervasive guard/`$type`-traffic
overhead.

**Solution (from the design note).** Heuristic monomorphisation at the
CIC₀/`Defhash` level — seed with ground constant instances from the goal,
saturate by matching against polymorphic premises, bound by rounds and
instance count (the Sledgehammer/Lean-auto recipe; every measured study
finds this beats both complete polymorphic encodings and native prover
polymorphism). Doing it at CIC₀ level (not FOL level) makes instantiated
bodies β-reduce, re-runs `check_prop` per instance (dissolving the
four-pairs problem), and regenerates *specialized* inversion/injectivity
axioms through the existing machinery — which after `notes/indexed_families.md`
includes the forded index equations, specialized per instance, for free.
Phase two fuses ground type arguments into predicate symbols
(`list_nat(x)`) — half of this already exists in `tptp_out.ml`'s
`tconst_hash`/`_$t` machinery. Phase three (optional, last):
monotonicity-based guard erasure with the precise soundness condition from
the literature (guard only variables of possibly-finite types occurring
naked in positive equations).

**Interaction note.** Monomorphisation multiplies axiom count while
shrinking each axiom; the indexed-families expansion multiplies formula
size per occurrence. Their screening axes must be crossed at least once
before defaults are chosen jointly.

---

## 2. Induction

**Gap.** The translation deliberately emits no induction
(`opt_induction_principles = false`, and rightly so as a *global* setting:
schemas are second-order). Consequently any goal whose FOL image needs a
least-fixed-point property is unprovable at the translation level, however
trivial. Verified microcosm: `n <> S n` — Rocq proves it only by induction
(directly, or via `Acc`-irreflexivity + subterm well-foundedness, which is
induction twice); `congruence` (= exactly our injectivity + discrimination
theory) fails on it, plain `sauto` fails on it, and the FOL theory we emit
has the `ω`-countermodel (`S ω = ω` satisfies injectivity, discrimination,
guarded inversion). Today such goals go through only if premise selection
happens to supply the induction-derived lemma.

**Solution space**, in increasing ambition:

- **(a) Goal-motive schema instances.** The induction schema instantiated
  with a concrete first-order motive is an ordinary FO axiom. Emit, for the
  goal's conclusion `G[x]` with `x` of inductive type `T` (and optionally
  for each premise-selected unary predicate over `T`), the instance
  `(⋀_c ∀ā. IH → G[c ā]) → ∀x. guard(x,T) → G[x]`, guard-relativized as
  everything else. Precedents: Isabelle passes induction rules as ordinary
  lemmas (with the known weakness that ATPs rarely find the motive —
  which is why we *pre-instantiate*); FOTC has the user instantiate the
  schema and ships each instance [R-enc §7]; Why3's `induction_ty_lex`
  splits the goal meta-level before dispatch [R-enc §8]. The motive-choice
  heuristic starts trivial (the goal itself, universally closed over its
  inductive-typed variables) and can grow (subformula motives,
  generalization by variable abstraction).
- **(b) Prover-native induction.** Vampire's `--induction` and cvc5's
  inductive strengthening accept plain FO problems and synthesize motives
  internally; enabling per-prover flags in `provers.ml` costs almost
  nothing and composes with (a). Zipperposition-style induction would come
  with the HO backend (§4).
- **(c) Meta-level goal splitting** (Why3-style): perform `induction` in
  Coq *before* invoking the hammer, one ATP problem per subgoal — this is
  really a `tacbest.ml`/reconstruction-search feature (`hammer` already
  searches tactic combinations; adding `induction x; hammer`-shaped
  candidates for goals with inductive-typed universals is cheap and needs
  no translation change at all).

**Recommendation.** Start with (c) + (b) — near-zero translation risk,
immediate coverage of the `n <> S n` class — then (a) behind
`opt_induction_instances` with a screening axis. Reconstruction is
unaffected: any ATP proof using an induction instance reconstructs with
`induction` + `sauto`, which is exactly what `tacbest` can be taught to
try when the instance was used.

---

## 3. Arithmetic and primitive types

**Gap.** `nat`, `N`, `Z`, `Q` reasoning goes through constructor axioms and
whatever stdlib lemmas premise selection picks — Peano arithmetic by
superposition, which is weak at even linear arithmetic side conditions.
Rocq primitives (`Uint63`/`Sint63`, `PrimFloat`, `PArray`, `PString`) are
opaque constants with no semantics at all.

**Solution.** A *typed* output path alongside untyped FOF:

- **TFF (TPTP typed, with `$int`/`$rat` arithmetic)** for Vampire and E;
  **SMT-LIB** for cvc5/Z3 (which also unlocks their native datatypes for
  fully monomorphic inductives — with the caveat from [R-enc §3] that SMT
  datatypes build in unguarded exhaustiveness, so only junk-free,
  fully-guarded fragments may map onto them).
- Injections: `nat`/`N`/`Z` map to `$int` with range guards (`0 ≤ n` for
  `nat`); `S`/`O`/`Z.add`… map to arithmetic terms; constructor axioms for
  mapped types are *replaced* by the theory (emitting both invites the
  matching-loop/duplication failure mode). `Uint63` maps to `$int` with
  modular-range guards or to SMT bitvectors; floats to SMT FP (or stay
  opaque initially — IEEE semantics is its own project); `PArray` to SMT
  arrays.
- Soundness story: the junk model already interprets these types; the new
  obligation is that the injection is an embedding on the guarded fragment
  — same structure as the existing guard soundness argument, plus the
  standard "don't let native `=` cross the injection boundary untyped"
  discipline (the F\* #1542 incident is the cautionary tale [R-enc §4]).

**Sequencing.** After §1: the type-guard fusion work in `tptp_out.ml` is
the same code path that a TFF printer needs (sorts = fused ground types),
and monomorphisation is what makes occurrences ground enough to map onto
theory sorts. Reconstruction: `lia`/`zify` cover the reconstruction side
for the integer fragment — `tacbest` gains `lia`-augmented variants.

---

## 4. Genuine higher-order goals

**Gap.** Lambda-lifting handles λs at *occurrences*, but goals quantifying
over functions/predicates, or needing extensionality, remain out of reach
(JAR §9). Premise-side HO lemmas (`map_ext`, `Forall_impl`-shaped) either
don't apply or apply only through the `@`-encoding with poor unification
behavior. §1 removes a large slice of this (instantiated HO parameters
β-reduce away); this section is about what remains after it.

**Solution space.**

- **(a) Native HO backends.** Emit TH0/HO-TPTP for Zipperposition, E-HO,
  Vampire-HOL. The translation is *easier* than FOF (λs and application
  are native; guards unchanged); the printer is new but small relative to
  `tptp_out.ml`. Sledgehammer's measured experience: HO provers win a
  distinct slice of goals, complementary to FO provers — run them in the
  existing parallel portfolio (`parallel.ml`), don't replace.
- **(b) Guarded extensionality axioms in the FO problem**:
  `∀f g. guard(f, A→B) → guard(g, A→B) → (∀x. guard(x,A) → f@x = g@x) → f = g`.
  Sound in the junk model only if the model's function fragment is
  extensional on guarded arguments — a real model obligation to check, not
  free (and the F\* funext incident [R-enc §4] shows exactly how the
  unguarded version dies: equality proven at one type leaking to another).
  Propositional extensionality similarly as `(P <=> Q) → P = Q` on the
  formula-as-term boundary — only if the model quotients props, which the
  junk model does (props denote the two-element set) — worth stating and
  screening, cheap.
- **(c) Better combinator/lifting hygiene** (incremental): supply
  extensionality-free instances of common HO lemmas at CIC₀ level by
  β-expanding premise-selected HO lemmas against goal subterms — a small
  monomorphisation-adjacent pass over function arguments rather than type
  arguments ("higher-order instantiation", what Lean-auto's λ→\*
  abstraction approximates from the other side).

**Recommendation.** (a) is the best value: additive, no soundness surface,
measurable immediately. (b) needs the model check first; (c) folds into
the §1 implementation as a follow-on axis.

---

## 5. Coinductives and corecursion

**Gap.** `CoInductive` types currently ride the inductive machinery
generically — unaudited rather than designed. Nothing is known-unsound
(we emit no acyclicity, no induction — the two things that are *false*
for codata), but nothing is principled either: cofix definitions get
whatever the fix path produces, and no coinduction-specific content
(bisimulation, uniqueness) exists.

**Solution** (small, precedented — [R-enc §7, §2]):

- **Inversion is sound for codata** and should be emitted exactly as for
  inductives: productivity gives canonicity, so every guarded inhabitant
  is constructor-generated — FOTC's `Stream-gfp₁` axiom
  (`Stream xs → ∃x' xs'. Stream xs' ∧ xs = x' ∷ xs'`) is the exact shape,
  in untyped FOL, with index equations if the family is indexed (the
  fording lens applies unchanged — nothing in `notes/indexed_families.md`
  §2 assumes well-foundedness).
- **Cofix unfolding must be destructor-guarded**: emit
  `head(s) = …`/`tail(s) = …` projections-of-unfolding rather than the raw
  `s = cons(a, s)` unit equation (the Dedukti discipline: unfold only
  under destructors [R-enc §9]; also avoids handing superposition an
  orientation-fragile self-referential equation).
- **Uniqueness/bisimulation only as per-goal instances** (the
  Reynolds–Blanchette codatatype uniqueness rule is a schema, same status
  as induction — §2's machinery applies dually).
- **Never any subterm/acyclicity reasoning for codata** (cyclic values are
  legal); if §6 lands, its `Sub` axioms must be generated for inductive
  types only — worth an explicit test.

**Priority**: low until a corpus shows demand; the audit (what does the
current generic path actually emit for a cofix?) should happen regardless
and is a half-day.

---

## 6. Term-algebra acyclicity

**Gap.** Goals needing `x ≠ c(…x…)` are not provable from the emitted
axioms — injectivity + discrimination + guarded inversion pin down a
locally-free algebra but admit cyclic models (the `ω`-countermodel:
`S ω = ω` satisfies everything we emit; the unguarded acyclicity statement
is even *false* in the junk model, since junk fixed points of `S` are
allowed). Acyclicity is a genuine schema — not finitely axiomatizable in
the constructor signature (Kovács–Robillard–Voronkov, POPL 2017 [R-ford
§7]) — and in CIC every instance is a theorem *by induction* (`Acc`
irreflexivity + subterm well-foundedness; verified: this is also exactly
where `congruence` and plain `sauto` give up).

**Solution**: the finitely-axiomatized conservative extension, guarded.
Per inductive type `T` (inductives only — see §5), a fresh predicate
`Sub_T` with:

    generation:     Sub_T(x_i, c(x̄))          for each constructor c,
                                               each recursive position i
    transitivity:   Sub_T(x,y) ∧ Sub_T(y,z) → Sub_T(x,z)
    irreflexivity:  guard(x,T) → ¬Sub_T(x,x)

from which every guarded acyclicity instance follows by unit resolution —
no schema. The irreflexivity axiom is `Acc_irrefl` with the induction
amputated: underivable in the emitted theory, sound to assert because the
intended (guarded fragment of the junk) model satisfies it.
Alternatives: prover-native term-algebra rules (Vampire
`--term_algebra_rules`, cvc5 datatypes) where the monomorphic/junk-free
mapping of §3 applies; bounded instance emission is dominated by the
`Sub` encoding and not worth building.

**Reconstruction**: an ATP proof using `Sub_T` axioms reconstructs via the
Equations-style `NoCycle`/`Derive Subterm` argument or simply
`induction` + `sauto`; `tacbest` should try these when `Sub` axioms were
used. **Trigger**: land behind `opt_acyclicity`, default off, and turn on
only if screening shows goals lost for want of it — the clause-size cost
(one transitivity axiom is a superposition menace) is real, which is why
this is trigger-driven rather than presumed.

---

## 7. Erasure completions: logical-argument and type-argument pruning

**Gap.** Erased arguments still occupy argument *positions*: a function
with a proof argument is translated at full arity with `$Proof` filling
the slot; after §1, ground type arguments similarly persist as dead
weight in every literal. Extraction proper *removes* these positions
(Letouzey's logical-argument pruning); the translation currently only
canonicalizes them. Every literal is bigger than it needs to be, and
clause size is exactly the currency recent regressions were paid in
(the refinement-expansion stdlib dip: 693→729 KB tipping threshold-noisy
cells).

**Solution.** A CIC₀-level signature-pruning pass mirroring extraction:
for each constant, compute the mask of argument positions that are
(after erasure) uniformly `$Proof` or (after §1) uniformly a fixed ground
type term, and translate the constant at reduced arity, rewriting all
occurrences. Subtleties, all known: (i) partial applications — the
multiple-arity machinery (`opt_multiple_arity_optimization`) already
handles per-arity symbol variants, so pruning composes with it rather
than fighting it; (ii) the pruned symbol's specification formula must be
re-derived from the pruned type (the guard generator already walks the
telescope — skip pruned binders); (iii) do *not* prune arguments that are
erased at some occurrences but not others (no per-occurrence arity
puns) — uniformity is the criterion, computed once per constant at
`Defhash` level; (iv) constructor argument pruning is exactly Letouzey's
`exist x ↦ x`-style optimization generalized, and for `CSubset` classes
it is already done by the refinement expansion — this item extends the
same idea to plain functions. `notes/extraction.md` already observes that
extraction's pruning subsumes parts of TODO 2/3/5/6; this is the concrete
remaining piece.

**Priority**: cheap, behavior-transparent (output-equisatisfiable by
construction), and its savings compound with §§1, 3, and the
indexed-families expansion. Do it early; measure as its own axis anyway
(clause-size effects have surprised us before).

---

## 8. Below the line

Deliberately not gaps worth a design: **SProp** (map to the Prop path;
its stricter elimination only *removes* cases — a correctness audit, not
a feature); **universe constraints** (ignored; the junk model doesn't
care, and no goal class is known to need them); **eta for primitive
records** (guarded surjective-pairing axioms if a corpus ever demands —
the Verus #1366 incident [R-enc §5] says treat degenerate/empty record
types carefully if so); **module/functor structure** (flattened to
constants before the translation sees it); **induction–recursion /
induction–induction** (not in Rocq); **quotients** (not in Rocq;
setoid-style reasoning arrives as ordinary premises).

## Cross-cutting

Every item above: (a) lands behind its own `opt_*` compile-time flag wired
into `eval/rebuild-config.sh`; (b) gets a leave-one-out screening axis and
a consistency-canary extension (prove-`$false` over dumps exercising the
new axioms — the §6 `Sub` axioms and §3 theory injections especially,
since both add *asserted-not-derived* content); (c) states its junk-model
obligation in the soundness paper before default-on. The
reconstruction side (`tacbest.ml`) grows in step: `induction`+`sauto`
variants (§2, §6), `lia`-augmented variants (§3) — reconstruction failure
is the silent killer of translation-side wins, and the eval harness
already measures end-to-end, which is the right metric for all of this.
