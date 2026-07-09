# Extraction evaluation notes

## Phase 6 Stage 1 screening (TASK_22, 2026-07-09)

Raw checkpoint data lives under
`/home/dev/coqhammer/worktrees/extraction/eval/results/stage1/`; the committed
summary artifacts are in
`/home/dev/coqhammer/worktrees/extraction/eval/artifacts/task22-stage1/`.

Scope: committed Stage-1 corpora from TASK_21 (`stdlib-regression`,
`dependent-slice`, `external-equations` samples), premise counts 64/256/1024,
provers E and Vampire, baseline merge-base plus all-on and five leave-one-out
configurations, each with declaration-level refinement skips off/on.

Baseline sanity gate: **passed**. The baseline install was the merge-base build;
it generated all three corpora and reproduced the TASK_21 dry-run shape on the
overlap (stdlib smoke remains solved by E at the small premise setting). Stage-1
baseline totals were 29/66 ATP successes (43.9%): stdlib 17/18, dependent slice
12/36, external 0/12. No harness debugging was needed before running the
refactor configurations.

Consistency scan: **0 hits**. Every generated `knn-64` problem in each
label/corpus checkpoint was rewritten to `$false` and scanned with E and Vampire
at a short timeout; no `SZS status Theorem` occurred. The two split-off external
checkpoints failed during ATP generation and therefore have no generated problems
to scan; this is recorded as a screened regression of the split-off ablation, not
as an inconsistency.

Winner: **`stage1-loo-erasure-guards-decl-skips`** (all refactor options on,
declaration-level skips on, `opt_erasure_guards=false`): 56/66 ATP successes
(84.8%). This is the Stage-1 candidate for TASK_23 confirmation.

Flagged options / regressions:

- Keep **declaration-level refinement skips on** for confirmation: all-on improves
  from 37/66 to 50/66 with skips, and the winning unguarded configuration improves
  from 43/66 to 56/66 with skips.
- `opt_erasure_guards=true` is the clearest regression: disabling it (unguarded
  transport equations) raises the decl-skip run from 50/66 to 56/66, including
  `dep_eq_rect_refl` from 0/6 to 6/6.
- Disabling split case equations is not viable: the external Program/WF sample
  was killed during ATP generation in both decl-skip settings, and the completed
  subset is below the winner (27/54 and 29/54).
- `opt_refinement_types=false` preserves stdlib arith/list smoke but loses the
  dependent/external wins; do not disable it for defaults.
- `opt_prop_case_erasure=false` is neutral with declaration skips (50/66, same as
  all-on-decl-skips) but slightly better without skips. Keep it under watch in
  TASK_23 rather than treating it as a default flip.
- `opt_wf_recursion_eqs=false` loses external/WF successes (44/66 with skips vs
  56/66 winner), so keep WF equations on.

Dependent-slice delta: winner 29/36 vs baseline 12/36, **+47.2 percentage
points**. The main visible wins are `dep_vector_head_cons` (0/6 -> 5/6),
`dep_fin_f1_zero` (0/6 -> 6/6), and `dep_eq_rect_refl` (0/6 -> 6/6); `dep_idiv_zero`
remains 0/6 in this small grid.

Equational/computational subsets:

- Arithmetic (`stdlib_nat_add_0_r`): baseline 6/6, winner 6/6.
- Lists (`stdlib_list_map_cons`): baseline 5/6, winner 6/6.
- Bool computation (`stdlib_bool_negb_involutive`): baseline 6/6, winner 3/6;
  this is the only stdlib-smoke regression and should be checked in TASK_23's
  confirmation grid.
- External Program/WF smoke: baseline 0/12, winner 12/12.

Problem-size/definition metrics are in `summary.tsv`; at the overall level the
winner averages 217 constants with `$_def_*` equations per row and about 862856
TPTP bytes/problem-row, with zero consistency hits.

## Phase 6 Stage 2 confirmation and final default decision (TASK_23, 2026-07-09)

Raw checkpoint data lives under
`/home/dev/coqhammer/worktrees/extraction/eval/results/stage2/`; the committed
summary artifacts are in
`/home/dev/coqhammer/worktrees/extraction/eval/artifacts/task23-stage2/`.

Scope: the Stage-1 winner versus the merge-base baseline over the committed
Phase-6 corpora (`stdlib-regression`, `dependent-slice`, `external-equations`),
using the full standard `hammer_hook` grid: `{knn, nbayes}` × premise counts
`{32,64,128,256,1024}` × the four provers E, Vampire, Z3, and CVC4.  ATP timeout
was 10s.  Reconstruction was run for every ATP-successful problem.

Important mid-run finding and mitigation: the first Stage-2 scan found one real
inconsistency in the candidate configuration (`dep_mset_empty`, Vampire,
`knn-1024`).  The proof used `ssrbool.introT` with an enum-expanded guard for the
indexed family `reflect`; the expansion had constructor payloads but omitted the
result-index constraint, allowing a `ReflectT P` witness at index `false`.  This
was not an `opt_erasure_guards`/transport issue.  The implemented mitigation is
conservative and sound: indexed Set/Type enum/subset families (for example
`reflect`) now stay on the regular guard path until index constraints are
represented in the shallow guard.  The full Stage-2 winner grid was then rerun
from scratch and the inconsistency scan was clean.

Headline ATP/reconstruction results after that fix:

| configuration | ATP successes | ATP rate | reconstruction on ATP successes | inconsistency hits |
|---|---:|---:|---:|---:|
| baseline merge-base | 196/440 | 44.5% | 196/196 (100.0%) | 0 |
| final defaults | 385/440 | 87.5% | 385/385 (100.0%) | 0 |

Per-prover ATP rates:

| prover | baseline | final defaults |
|---|---:|---:|
| E | 50/110 (45.5%) | 100/110 (90.9%) |
| Vampire | 50/110 (45.5%) | 100/110 (90.9%) |
| Z3 | 47/110 (42.7%) | 100/110 (90.9%) |
| CVC4 | 49/110 (44.5%) | 85/110 (77.3%) |

Per-corpus ATP rates:

| corpus | baseline | final defaults |
|---|---:|---:|
| stdlib regression | 117/120 (97.5%) | 120/120 (100.0%) |
| dependent slice | 79/240 (32.9%) | 191/240 (79.6%) |
| external Program/WF sample | 0/80 (0.0%) | 74/80 (92.5%) |

Metrics required by PLAN §12.3:

- ATP success rate per prover: recorded above and in `summary.tsv`; every prover
  improves over baseline.
- Reconstruction rate on ATP-successful problems: 100% for both baseline and
  final defaults.  Newly found final-default ATP successes absent from baseline:
  191; reconstructed: 191 (100.0%).
- `eq_rect` watch: `dep_eq_rect_refl` moves from 0 ATP successes to 37, and all
  37 reconstruct.  There is no ATP-up/reconstruction-down gap, so D3 does not
  trigger `opt_erasure_guards := true`.
- Constants with `$_def_*` equations: unique def-bearing constants in generated
  problems go from 1113 (baseline) to 1117 (final defaults); winner-only examples
  are `Corelib.BinNums.PosDef.Pos.add_carry`, `Corelib.Init.Wf.Acc_rect`,
  `Stdlib.Sets.Relations_1.Order_rect`, and `program_equations_smoke.fuel_drop`.
- Problem sizes: average generated TPTP size over grid rows increases from
  421,605 bytes/problem to 548,698 bytes/problem; maximum size increases from
  3,470,827 bytes to 8,846,736 bytes.  This cost did not produce an ATP
  regression on the confirmation corpus.
- Inconsistency scan: after the indexed-enum mitigation, exhaustive false-goal
  scans of every Stage-2 generated problem in these corpora with E and Vampire
  produced 0 `SZS status Theorem` hits (440 scanned problem/prover inputs).

Verdict against PLAN §12.4:

1. Overall ATP success rate ≥ baseline: **PASS** (`87.5%` vs `44.5%`, +43.0 pp).
   The equational/computational stdlib subset also does not regress (`100.0%` vs
   `97.5%`; the Stage-1 bool regression disappears in the full grid).
2. Dependent slice strict improvement: **PASS** (`79.6%` vs `32.9%`, +46.7 pp).
   The external Program/WF sample also improves from `0.0%` to `92.5%`.
3. Reconstruction rate on newly found proofs comparable to overall: **PASS**
   (newly found proofs reconstruct at `100.0%`, same as overall ATP-successful
   reconstruction).  `dep_idiv_zero` itself remains unsolved in this small
   dependent-slice fixture, but the WF external sample supplies the measured WF
   win and no reconstruction gap appears.
4. Zero inconsistencies: **PASS after mitigation**.  The initial indexed
   `reflect` hit was fixed by regular fallback for indexed enum/subset families;
   the rerun scan is clean.

Final default decision in `src/plugin/coq_transl_opts.ml`:

- `opt_split_case_axioms = true`: confirmed.
- `opt_prop_case_erasure = true`: confirmed; no Stage-2 inconsistency after the
  indexed enum/subset mitigation, and it remains part of the dependent-slice win.
- `opt_erasure_guards = false`: confirmed; unguarded transport gives the
  `eq_rect` ATP win and all such successes reconstruct.
- `opt_refinement_types = true`: confirmed; required for the dependent/external
  gains.
- `opt_refinement_decl_skips = true`: flipped on by default; Stage 1 selected it
  and Stage 2 confirms the winner with zero inconsistencies.
- `opt_wf_recursion_eqs = true`: confirmed; the Program/WF sample improves
  sharply and the false-goal scans stay clean.

Merge posture (D6): land this work on `rocq-9.2`; forward-port to `master` after
that.  A `rocq-9.1` backport remains optional and should be a separate user
release decision.  No merge or port was performed as part of TASK_23.
