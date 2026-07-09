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
