# Bounded inclusion of definitions of goal and hypothesis constants in premise selection

*Design note, 2026-07-18. Question: the FOL translation leaves unselected
constants uninterpreted, so a goal or hypothesis mentioning `f` is useless to
the ATPs unless `f`'s defining axioms are selected — how do we include the
definitions of goal/hypothesis constants in a principled, efficient way,
without overloading the selected premises unboundedly? Sources: four research
reports in `notes/research/` — `premise-selection-coqhammer-dataflow.md`
[R-coq], `premise-selection-sledgehammer.md` [R-sh],
`premise-selection-leanhammer.md` [R-lean],
`premise-selection-literature.md` [R-lit] — and the papers archived in
`notes/papers/` (Meng–Paulson 2009, MaSh ITP13/JAR16, SInE CADE 2011,
CoqHammer JAR 2018, LeanHammer 2025, lean-auto CAV 2025, DeepMath,
Magnushammer, ReProver, Graph2Tac, Flyspeck JAR 2014). Context: the naive
unbounded force-union of direct goal dependencies was reverted in d4b6a40
("Remove forced direct-dependency premises; restore predictor contract").*

## TL;DR

Two mechanisms, independently optioned, both strictly inside the existing
premise budget N:

1. **Reserved definitional slots (primary)**: per prediction, carve
   `k = min(|D|, K, ⌈N/8⌉)` slots out of the N-premise budget for a
   deterministic, *rarity-ranked* list D of definitions of constants
   occurring in the goal and hypotheses (depth 1); fill the remaining
   `N − k` slots from the predictor ranking, dropping its tail. `K` is a new
   runtime option (`Set Hammer DefinitionPremises`, default 32; 0 disables
   → exact current behavior). The total never exceeds N, so the GSMode
   ladder's 32/64/…/1024 budgets and eval comparability are preserved —
   this is precisely what the reverted d4b6a40 feature failed to do.
2. **Definitional feature expansion (phase 2, separate screening axis)**:
   enrich the goal's query feature vector with the features of the
   *definitions* of its rare constants, so the learned rankers see through
   a fresh `f` to its body — the feature-level analogue of DeepMath's
   def-CNN and of Graph2Tac's definition task, and exactly what Magnushammer
   names as its own missing piece.

No translation changes; no C++ predictor changes; no soundness surface.

---

## 1. The problem, precisely

Facts established in [R-coq]:

- All hypotheses are always passed to the ATPs
  (`hammer_main.ml:773-774`); only `deps1` (the selected definitions and
  lemmas) is subject to premise selection. Axioms are emitted only for the
  goal, hypotheses, and selected premises (`get_axioms`,
  `coq_transl.ml:2465-2471`); every other constant appearing in them is an
  **uninterpreted FOL symbol**. So a hypothesis `H : f x = g x` contributes
  nothing unless `f`/`g`'s entries are selected.
- The learned predictors *can* select definitions — every accessible
  definition is a fact in the per-invocation corpus, kNN scores neighbors
  themselves (`knn.cpp:64-89`), and naive Bayes learns each fact as its own
  dependency with weight 1000 (`nbayes.cpp:97-100`). But there are
  systematic blind spots:
  - **A non-recursive fresh definition's entry does not contain its own
    name as a feature.** The entry's features are the symbols of its type
    and body (`get_def_fea_term`, `features.ml:123-128`); `f` itself occurs
    among them only when `f` is recursive. A goal about `f` overlaps such an
    entry only via the body's symbols — weak, noisy, and diluted exactly
    when the body is large.
  - The predictor drops query features absent from its symbol table
    (`format.cpp:143-153`), so a goal constant that appears in *no*
    accessible entry's features contributes nothing to similarity.
  - Ranked competition at the small end of the GSMode ladder (32/64
    premises) means even a well-scored definition can miss the cut on
    feature-poor goals.
- The corpus-level evidence that this matters is CoqHammer's own JAR 2018
  conclusion [R-lit §1]: the same selectors need **~499–530 premises** to
  cover dependencies on the Coq stdlib versus 200–300 on HOL/Isabelle
  corpora, and the paper explicitly flags that learned dependencies miss
  "definitions of constants, facts which are necessary to establish types
  of certain terms."
- The codebase already contains a depth-1 definitional union — but only on
  the given-lemmas path: `choose_given_lemmas` (`features.ml:226-244`)
  takes {lemmas} ∪ {their direct deps} ∪ {direct deps of goal} ∪ {direct
  deps of each hypothesis}, uncapped. The reverted d4b6a40 feature applied
  the same set on the main path *in addition to* the N predictions; the
  objection was the broken budget, not the idea.

## 2. What the other hammers do (and don't)

Compressed from [R-sh], [R-lean], [R-lit]:

- **Nobody force-includes definitions of goal constants.** Sledgehammer's
  MePo paper tried exactly that ("definition expansion": force-relevance of
  oriented unit def-equations of relevant constants) and found it
  "beneficial, but its effect is small"; it is **not** in the current code,
  and `Non_Rec_Def`/`Rec_Def` statuses carry **no** MePo bonus [R-sh §1-2].
  The Lean stack likewise has no "goal constant → add definition" rule
  [R-lean].
- **Definitions are first-class ranked facts everywhere.** Sledgehammer's
  pool contains `f_def`/`f.simps` as ordinary facts; LeanPremise's corpus
  contains definitions, with `rw`/`simp` usage in the training signal; a
  *selected* definition is then expanded to equations at fact-elaboration
  time (Duper `elabFact`, lean-auto `d[...]`). CoqHammer's translation
  already does this expansion for selected entries (`add_def_eq_axiom`), so
  only the *selection* side needs work.
- **The budget is sacred.** All bounding in mature systems is a single
  ranked list truncated per prover slice at empirically tuned sizes
  (Sledgehammer 16–2048; CoqHammer 32–1024). True reserved slots exist but
  are tiny and deliberate: user `add:` facts at the head, and MePo's 3–4
  special facts inserted at fixed index 45 and re-truncated to the budget
  [R-sh §2] — reserved slots *within* N, never additions to N.
- **Freshness is handled by dedicated bounded channels, not closure.**
  MaSh blends in a proximity component (the 100 most recently defined
  facts, weight 0.4; chained facts 0.9) precisely because "new facts will
  typically appear in few proofs, regardless of how useful they may be"
  [R-sh §4]; LeanHammer's symbolic fallback interleaves SInE 50/50 with a
  `currentFile` selector [R-lean §2]; Graph2Tac computes embeddings for new
  definitions from their bodies in topological order, worth 1.5× on unseen
  packages, with the gain growing in the number of new dependencies
  [R-lit §4].
- **The principled bounded closure is SInE** [R-lit §5]: from goal symbols,
  add axioms *owned* by reached symbols (ownership = least-common symbol in
  the axiom, slack `t`, depth `d`). Empirically: tolerance is the stable
  knob (t ≈ 1.2–3), depth is powerful but fragile, the generality threshold
  was droppable. Its known failure mode is exactly ITP-style goals with
  many symbols (Mizar goals trigger >4000 axioms even at d = 1) — which is
  why we adopt only its *ownership/rarity* idea, under a hard cap, rather
  than the closure itself.
- **Two-phase pipelines are the norm at the top**: learned ranking bounds
  the space, then a symbol-based device re-prunes or backfills (MeSh's
  0.5/0.5 abstention-aware mixing; BliStr-evolved E strategies running SInE
  depth 1–2 *inside* the ATP in 11–12 of the 14 best strategies)
  [R-lit §7].

## 3. Design principles

1. **Respect the budget.** Any deterministic inclusion carves slots out of
   the candidate's N, never adds to it. The GSMode ladder entries keep
   their meaning; eval remains comparable to the baseline; d4b6a40's
   objection is structurally impossible to re-trigger.
2. **Rarity-first, SInE-style.** The blind spot is rare and fresh
   constants; common constants (`nat`, `eq`, `list`, …) are both
   well-covered by the learned ranking and the classic way to blow up the
   premise set (Sledgehammer treats common set constants as *built-in*
   rather than relevant precisely because they "tend to pull in too many
   irrelevant facts"). Under a cap, priority must go to the constants the
   learned channel is worst at.
3. **Depth 1 by default.** SInE's own data says depth is the fragile
   parameter; MePo's iteration and the predictors' body-feature overlap
   already provide a soft depth-2 signal; and the translation pulls
   structural theories of scrutinee inductives on its own
   (`Case_dependencies` [R-coq §5]). Deeper closure is a later, separately
   measured extension.
4. **Selection-level, not translation-level.** The translation already
   expands whatever is selected; putting the mechanism in `features.ml` /
   `hammer_main.ml` keeps it optionable, evaluable per candidate, and free
   of soundness surface. (A translation-level unconditional closure would
   affect all candidates identically and unboundedly — rejected.)
5. **Every knob measurable.** One runtime option with 0 = exact current
   behavior; a screening axis before any default is finalized, per the
   established eval methodology.

## 4. Mechanism A: reserved definitional slots

### 4.1 Candidate set D

Computed once per invocation (not per GSMode candidate), on the same data
`choose_given_lemmas` uses:

- **Seed** S = constants occurring in the goal statement and in every
  hypothesis statement (and let-bound hypothesis bodies) —
  `get_deps goal ∪ ⋃ get_deps hyp`, filtered to nontrivial accessible
  definitions exactly as in `choose_given_lemmas` (`features.ml:226-244`).
  Uncached for goal/hyps (they are proof-local; the existing comment
  applies).
- **Grouping rule**: a seed constant that is a constructor also pulls its
  inductive type's entry; a seed constant that is an inductive type also
  pulls its constructors' entries (each group member occupies its own slot).
  Rationale [R-coq §5]: selecting an `IndType` yields
  injection/discrimination/inversion axioms mentioning constructors, but a
  constructor's *typing axiom* is emitted only if the constructor itself is
  selected; conversely a constructor without its inductive loses the
  structural theory. lean-auto's monomorphizer similarly auto-collects
  constructor/recursor facts for inductive instances it meets [R-lean §4].
- D = the seeded (and grouped) entries, as `hhdef`s.

### 4.2 Ranking within D

Primary key: **rarity, ascending occurrence count** —
`occ(c) = |{d ∈ defs : c ∈ deps(d)}|`, computable from the dependency table
`extract` already builds (`features.ml:189-224`; the deps cache makes this
one fold). This is SInE's ownership/generality measure and the IDF the
predictors already trust, applied to slot priority: the rarer the constant,
the less the learned channel knows about it, the more it needs the slot. A
fresh definition has occ = 0 and ranks first automatically — the
proximity/currentFile channels of MaSh and LeanHammer fall out as a special
case rather than needing a separate recency mechanism (the per-invocation
retraining already makes fresh facts *visible*; rarity makes them
*prioritized*).

Secondary key (tiebreak): **definition size, ascending** — node count of
the hhterm body (type for opaque entries, whose bodies the translation
discards anyway [R-coq §1]). Prefers cheap unfoldings when slots are
scarce; large definitions still enter when slots allow, they just don't
crowd out small ones.

Explicitly *not* filtered out: opaque constants (their statement/typing
axiom is still valuable) and Prop-sorted lemmas that happen to occur in
statements (their statement is the axiom). Explicitly excluded: everything
`is_nontrivial` already excludes (logic constants, filtered modules).

### 4.3 Budget carve-out and merge

For a prediction with premise budget N (a GSMode ladder count, or
`predictions_num` on the non-GS path):

```
k       = min(|D|, K, ceil(N / 8))         (K = Opt.definition_premises)
forced  = first k of D (ranked as in 4.2)
rest    = predictor ranking minus forced, first (N − k)
premises = forced @ rest                    (|premises| ≤ N always)
```

- The 1/8 fraction keeps small candidates honest (N = 32 → at most 4 forced
  slots; N = 1024 → capped by K = 32), mirroring the scale of
  Sledgehammer's only real reserved-slot mechanism (3–4 special facts at
  index 45 out of ~50+ slots) [R-sh §2].
- Deduplication is against the predictor list: when the predictor already
  ranks a forced definition in its top N − k, the slot effectively costs
  nothing (the union is what it would have been).
- **Prerequisite: preserve the predictor's ranking.** `run_predict`
  currently intersects the output with `defs` and returns *defs order*
  (`features.ml:289`), destroying the rank order the C++ binary emits.
  The merge must drop the predictor's *tail*, not arbitrary elements —
  change `run_predict` to map the output names through a name→def table in
  output order. (Behavior-neutral on its own: the ATP receives a set.)
- GSMode: `dcands` and the occ table are computed once in `do_predict`
  next to the single `Features.extract` call (`hammer_main.ml:849-865`);
  each candidate closure applies the merge with its own N. Non-GS path:
  same merge around `Features.predict`. Given-lemmas (`Choice`) path:
  **unchanged** — it is user-directed and already includes depth-1
  definitions; imposing the cap there would silently drop material the
  user pointed at. (A separate cap option for that path is possible later
  if uncapped behavior proves problematic.)

### 4.4 Options and defaults

- `Set Hammer DefinitionPremises <int>` — the cap K. Default **32**;
  `Unset` → 32; **0 disables the mechanism entirely** (bit-for-bit current
  behavior, the eval baseline). Runtime option in `opt.ml` following the
  `predictions_num` pattern (selection options are runtime; only
  translation options are compile-time).
- No depth option initially (depth is fixed at 1 by design principle 3).
  If screening ever motivates depth 2, the right form is SInE's tolerance
  trigger (`occ(c′) ≤ t · min-occ` within the definition body), not blind
  closure — deferred.

### 4.5 What this buys, concretely

For the first goal about a fresh non-recursive `f` (the exact case where
[R-coq §2] shows the similarity signal is weakest): `f` has occ ≈ 0, ranks
first in D, and occupies one guaranteed slot in *every* candidate of the
ladder, including the 32-premise ones. For a goal whose hypotheses mention
a handful of project-specific constants, those definitions ride along in
≤ 4–32 slots while 96%+ of the budget still comes from the learned ranking.
For stdlib-heavy goals whose constants are all common, D's members are
mostly already in the predictor's top N and the mechanism is a near-no-op —
the failure mode of the reverted unbounded union (hundreds of forced
premises swamping the problem) cannot occur.

## 5. Mechanism B (phase 2): definitional feature expansion

The learned channel's underlying defect — a fresh constant's name carries
no information, and its entry's features don't contain its name — can also
be attacked on the *feature* side: extend the goal's query feature vector
(`get_goal_features`) with the features of the definitions of its rare
constants, i.e. let the query for `myrev (myrev l) = l` also contain
`app`, `cons`-shapes, etc. from `myrev`'s body. This is the feature-level
analogue of DeepMath's def-CNN (embed the symbol by its defining statement)
and Graph2Tac's definition task — the two mechanisms with the strongest
measured effect on unseen material in the literature [R-lit §4] — and it is
precisely the improvement Magnushammer's authors name as future work.

Bounds and caveats:

- Expand only constants with `occ(c) ≤ g` for a small generality bound g
  (rare constants; expanding `nat` would only add noise), and only their
  plain symbol features (not the polarity/pair features, which would be
  wrong across the definition boundary).
- The predictor protocol has no query-side feature weights
  ([R-coq §4]: the conj file is a plain feature list), so expanded
  features are indistinguishable from genuine goal features and can dilute
  the query. This is the reason B is phase 2 behind its own option and
  screening axis, not part of A: A's worst case is a handful of wasted
  slots; B's worst case is a degraded ranking for *all* N slots.
- Implementation is small: a variant of `get_goal_features` that appends
  `get_def_features_cached` of the selected rare constants; option
  `Set Hammer DefinitionFeatures` (default off until screened).

## 6. Alternatives considered and rejected

- **Unbounded union of direct dependencies** (the reverted d4b6a40
  feature): breaks the budget contract; MePo's history independently
  documents that force-including even ~100 small facts hurts the ATP
  search space [R-sh §1].
- **Translation-level unconditional closure** (Case_dependencies-style for
  goal constants): unbounded, unoptionable per candidate, moves selection
  policy into the translation. Rejected by design principle 4.
- **Full SInE selector as a new prediction method** (`-p sine` in the C++
  binary or OCaml-side): genuinely principled, but its known failure mode
  is ITP-style goals (huge triggered sets), and the ladder already provides
  the diversity SInE would add. The cheap, stable part of SInE — ownership
  by rarity — is exactly what A's ranking adopts. Could be revisited as a
  ladder *method* later; not now.
- **Score boosting instead of reserved slots** (MeSh-style mixing): needs a
  calibrated score interface the predict binary doesn't expose (it returns
  a ranked name list, no scores). Reserved-slots-with-backfill is the
  discrete equivalent MaSh itself uses for its unknown-fact components
  (`take (max_facts − length sels) unks`) [R-sh §5].
- **Predictor-side (C++) changes** (proximity prior, goal-dependency
  hints, query weights): larger blast radius, harder to option and
  evaluate; nothing in the design requires them. Query-side weights would
  unlock a better mechanism B — worth considering only after B's cheap
  form is measured.
- **MaSh-style recency component**: subsumed — per-invocation retraining
  already makes fresh facts visible, and occ-ranking already puts fresh
  facts first in D.

## 7. Implementation sketch

All in `src/plugin/`; no dune/C++/theories changes.

1. `features.ml`:
   - `occurrence_counts : hhdef list -> (string, int) Hashtbl.t` — one fold
     over `get_deps_cached` of the nontrivial defs.
   - `definitional_candidates : hhdef list (*hyps*) -> hhdef list (*defs*)
     -> hhdef (*goal*) -> hhdef list` — seed, group, rank (§4.1–4.2).
   - `run_predict`: return predictions in the predictor's output order
     (name→def table instead of the `List.filter` at `:289`).
   - `merge_def_slots : hhdef list (*ranked D*) -> int (*n*) ->
     hhdef list (*ranked predictions*) -> hhdef list` — §4.3 formula,
     reading `!Opt.definition_premises`.
   - `features.mli`: export the new functions; document the ranking
     contract of `run_predict`.
2. `opt.ml`: `definition_premises = ref 32` + `Set Hammer
   DefinitionPremises` declaration (pattern of `predictions_num`,
   `opt.ml:3-16`).
3. `hammer_main.ml` (`do_predict`, `:849-865`): compute
   `dcands = Features.definitional_candidates hyps deps goal` beside
   `Features.extract`; GSMode candidate closure becomes
   `fun () -> Features.merge_def_slots dcands preds_num
   (Features.run_predict fname deps preds_num pred_method)`; same wrap on
   the `gs_mode = 0` path. `do_choice` untouched.
4. Tests (`tests/plugin/`): a file with a fresh non-recursive definition
   whose goal needs unfolding (e.g. `Definition dbl n := n + n.` /
   `Lemma dbl0 : dbl 0 = 0.` via `hammer`/`predict`-level check), plus a
   `Set Hammer DefinitionPremises 0.` registration line to keep the option
   parsing covered.
5. Eval: add a screening axis `def-slots ∈ {0, 8, 32}` (and later
   `def-features ∈ {off, on}` for B) to the screening grid; the
   committed-measurement gap (issues.md item 7) means the confirmation run
   that eventually lands should already include the chosen default. The
   signature to watch: gains concentrated on goals whose statements mention
   constants with low occ (first-lemma-about-a-definition slices);
   regressions, if any, at N = 32 candidates where slots are scarcest.

## 8. Soundness and invariants

Selection-only: every forced premise is an accessible definition that the
translation would accept from the predictor anyway; the translation,
reconstruction, and minimization phases are untouched. The premise count
never exceeds the candidate's N, so ATP problem sizes stay within the
regime the ladder was tuned for. With `DefinitionPremises 0` the premise
lists are bit-for-bit those of today's code.
