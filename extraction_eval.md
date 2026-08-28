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

## 2026-08-23--28 — TASK_10 indexed-family extraction evaluation

This is the post-TASK_09 evaluation at candidate commit
`5cb0bfd36c7f14149ee2fd9f09d188a8c69b1a6a`.  Its pre-candidate baseline is the
merge base `790aaa110b601313c85430432b1bf02361cc6e16`.  It supersedes the small
three-corpus Stage-2 measurements above for deciding whether the new indexed
family extraction work is ready: the confirmation below uses all seven full
corpora and all 40 ATP cells per goal.

### Reproducibility and evidence

Environment: Rocq 9.2, OCaml 5.3.0, `rocq-stdpp` 1.13.0, `rocq-color` 1.8.6,
and Equations commit `c4e99d8953cee0396a391fe017204bbc2af1fb88`.  The normal
workspace-local `_opam` switch was retained.  Because the host opam metadata
root became read-only during setup, its metadata was copied to ignored
`.opam-root` and the already cached local Rocq repository was registered there;
package contents and the workspace prefix remained the same.

The baseline was run first in an ignored detached worktree at `790aaa1`, before
any candidate grid.  The large per-attempt/per-goal baseline and candidate
snapshots are ignored, workspace-local audit material under
`eval/results/task10-evidence/`; they are not repository-preserved evidence.
The tracked compact record is
`eval/artifacts/task10-comparison/{report.md,common-key-stats.tsv,provenance.env}`.
It preserves chronology, source-snapshot and generated-artifact digests,
common-key statistics, and the claims below without the 45 MiB attempt tables.
The candidate screening and confirmation summaries cited here are also tracked
under `eval/artifacts/extraction-{screening,confirmation}/`.

The baseline snapshot has 276,560 attempt rows, 80,580 successful ATP attempts,
70,371 successful reconstructions, 6,914 goals, 3,447 ATP-solved goals, and
3,091 goals reconstructed at least once.  The candidate has 276,840 attempt
rows, 80,454 successful ATP attempts, 70,241 successful reconstructions, 6,921
goals, 3,448 ATP-solved goals, and 3,092 goals reconstructed at least once.
Their exact snapshot and generated-summary digests are in the tracked compact
provenance.  The ATP totals were asserted equal to each run's generated
`summary.tsv`.

The only baseline/candidate corpus-content difference is intentional: baseline
`dependent-slice` predates the seven TASK_09 fixtures.  The other six corpus
digests match exactly, as do Equations examples and all scripts/timeouts.  All
baseline comparisons below therefore use the 276,560 common attempt keys and
6,914 common goal names unless explicitly labelled “new fixture”.

Principal commands (from `eval/`) were:

```sh
# in the detached merge-base worktree, then in the candidate worktree
./evaluate.sh confirmation -j 24 --tim 10 \
  --consistency-tim 2 --compile-timeout 43200

# candidate option screening
./evaluate.sh screening -j 12 --tim 5 \
  --consistency-tim 2 --compile-timeout 43200

# selected candidate confirmation
./evaluate.sh confirmation -j 24 --tim 10 \
  --consistency-tim 2 --compile-timeout 43200
```

Generation at `-j 24` exceeded available memory for several large corpora.
Those failed attempts were left in the workspace-local checkpoints, not treated
as measurements; each incomplete corpus was resumed at `-j 8` until its
validated `generate.done`, after which the prover/reconstruction grid resumed
at `-j 24`.  The baseline completed on 2026-08-25 and the candidate confirmation
on 2026-08-28.  The generated summaries are tracked in
`eval/artifacts/extraction-{screening,confirmation}/`; raw checkpoints are
ignored workspace-local data under `eval/results/{screening,confirmation}/`.

A real harness defect was exposed by the unsafe screening configurations: after
a genuine consistency hit, `grid-engine.sh` returned before publishing
`consistency-outputs-*.lst`, so the summarizer mistook a complete measured hit
for an incomplete run.  The fix publishes and validates the complete output set
before interpreting any hit.  Its regression test covers multiple outputs and
rejects a hit followed by an incomplete output.  The tracked compact provenance
also records the SHA-256 of the historical rerun patch; the patch itself remains
workspace-local audit material.

### Complete screening and option contributions

The screening grid contains 15 labels: `current`, plus all-off, all-on, and
leave-one-out configurations for Prop-case erasure, erasure guards, refinement
types, indexed families, and rigid-clash pruning, with declaration skips off
and on for each non-current configuration.  Each label has 108 ATP attempts
(18 sample goals × `knn-{64,256,1024}` × `{E,Vampire}`) and 36 consistency
outputs (18 `knn-64` false-conjecture problems × both provers).  All 270 summary
rows completed.

The final column below is the mean problem size over `knn-256` and `knn-1024`,
counting each generated problem once rather than once per prover.

| configuration | ATP / 108 | goals / 18 | consistency hits / 36 | high-premise mean bytes |
|---|---:|---:|---:|---:|
| current | **86** | **15** | 0 | 1,801,053 |
| all-on | 78 | 14 | 2 | 1,820,233 |
| all-on + declaration skips | 80 | 14 | 0 | 1,819,968 |
| leave out Prop-case erasure | 71 | 13 | 2 | 1,800,089 |
| leave out Prop-case erasure + skips | 74 | 13 | 0 | 1,799,824 |
| leave out erasure guards | 83 | 15 | 2 | 1,801,314 |
| leave out erasure guards + skips | **86** | **15** | 0 | 1,801,053 |
| leave out refinement types | 67 | 12 | 0 | 1,696,281 |
| leave out refinement types + skips | 67 | 12 | 0 | 1,696,281 |
| leave out indexed families | 79 | 14 | 0 | 1,810,444 |
| leave out indexed families + skips | 79 | 14 | 0 | 1,810,233 |
| leave out rigid-clash pruning | 78 | 14 | 2 | 1,820,939 |
| leave out rigid-clash pruning + skips | 80 | 14 | 0 | 1,820,674 |
| all-off | 61 | 11 | 0 | 1,673,318 |
| all-off + declaration skips | 61 | 11 | 0 | 1,673,318 |

Using all-on + declaration skips as the controlled reference, Prop-case erasure
contributes +6 ATP attempts and +1 solved goal; unguarded erasure contributes +6
attempts and +1 goal; refinement types contribute +13 attempts and +2 goals;
indexed-family extraction contributes +1 attempt and no union-level goal;
rigid-clash pruning is ATP/goal neutral in this sample.  At 256/1024 premises,
indexed extraction adds only 0.54% mean bytes relative to its leave-one-out
configuration.  Rigid-clash pruning saves 0.04%.  The current configuration is
exactly the successful leave-erasure-guards-out + declaration-skips cell and is
both the attempt-level and goal-level screening winner.  Its extra solved goal
over guarded all-on is `dep_eq_rect_refl`.

All eight screening hit incidences were the same canary,
`dep_ibval_bound`, reported once by E and once by Vampire in each of four
no-declaration-skip configurations (all-on and leave out Prop erasure, guards,
or pruning): 2/36 consistency checks = 5.56%, and 1/18 unique canaries = 5.56%
for each affected label.  Every declaration-skip label was clean.  Feature-off
labels that do not emit the problematic refinement declaration were also clean;
that does not make no-skips safe.  For comparison, the pre-change full grid was
clean at 0/14,660 checks, and the selected candidate full grid is clean at
0/14,800.  Consistency is not used as an absolute performance gate, but here
there is no tradeoff to justify the hit-producing variants: declaration skips
are both safer and faster.

### Selected winner and full confirmation

**Winner: current defaults**, equivalently leave erasure guards out with
refinement declaration skips enabled.  This choice is principled rather than a
single-ATP tie break: it leads both screening metrics, has zero consistency
hits, preserves the `eq_rect` gain, and emits smaller formulas than guarded
all-on.  No defaults were changed by TASK_10.

The complete selected grid covers `stdlib-regression`, `dependent-stdlib`,
`stdpp`, `color-vector`, `dependent-slice`, `equations-examples`, and
`external-equations`: 280 corpus/selector/prover cells and 40 attempts per goal.

| metric | baseline | candidate |
|---|---:|---:|
| ATP attempts | 80,580 / 276,560 (29.137%) | 80,454 / 276,840 (29.062%) |
| reconstruction on ATP attempts | 70,371 / 80,580 (87.33%) | 70,241 / 80,454 (87.30%) |
| goals solved by any ATP cell | 3,447 / 6,914 | 3,448 / 6,921 |
| goals reconstructed by any cell | 3,091 / 6,914 | 3,092 / 6,921 |
| consistency | 0 / 14,660 | 0 / 14,800 |

The extra 280 candidate attempts are exactly seven new dependent fixtures × 40.
On common attempts, candidate ATP successes are 80,282 versus 80,580: 516 newly
successful cells, 814 lost cells, net -298 (-0.108 percentage points on the
common denominator).  At goal-union level it gains seven old goals and loses
eleven, net -4 on the common 6,914 goals.  The seven gains are four
reconstructable by some cell; seven of the eleven lost goals had reconstructed
in baseline.  Adding the new fixtures gives the displayed total net +1 goal:
five of seven new fixtures are ATP-solved and all five reconstruct.

Per-corpus ATP rates (the dependent-slice total is not directly comparable
because of the seven added goals):

| corpus | baseline | candidate |
|---|---:|---:|
| color-vector | 3,437 / 12,480 (27.54%) | 3,450 / 12,480 (27.64%) |
| dependent-stdlib | 23,911 / 70,880 (33.73%) | 23,770 / 70,880 (33.54%) |
| equations-examples | 695 / 3,320 (20.93%) | 695 / 3,320 (20.93%) |
| external-equations | 681 / 1,960 (34.74%) | 682 / 1,960 (34.80%) |
| stdlib-regression | 25,849 / 44,840 (57.65%) | 25,760 / 44,840 (57.45%) |
| stdpp | 25,803 / 142,840 (18.06%) | 25,722 / 142,840 (18.01%) |
| dependent-slice | 204 / 240 common-fixture attempts | 203 / 240 common; 375 / 520 including new |

The overall -0.075 point ATP movement is small, but it is not hidden: common
old goals regress by four at union level, with the largest attempt losses in
Z3 (-132 including new fixtures, and -262 lost versus 95 gained on overlap),
dependent-stdlib, stdlib-regression, and stdpp.  Conversely CVC4 is fractionally
up in the total grid.  This should be treated as a near-neutral confirmation
with a small negative old-goal signal, not as an aggregate ATP improvement.

Formula growth does not explain a resource blow-up.  On the 69,140 common
generated problems (one copy per selector, not four prover copies), mean size
changes from 618,985 to 618,835 bytes (-0.024%).  On 256/1024 cells it changes
from 1,361,516 to 1,361,357 bytes (-0.012%).  The maximum changes from
12,482,310 to 12,501,363 bytes (+0.15%).  The largest corpus mean decrease is
Equations examples (-3.91%); dependent-stdlib and stdlib-regression each grow
about 0.11%, and stdpp grows 0.01%.

### New indexed fixtures and reconstruction inspection

New-fixture ATP/reconstruction cells are:

| fixture | ATP successes / 40 | reconstructions |
|---|---:|---:|
| `dep_cast_compose` | 40 | 40 |
| `dep_cast_refl` | 40 | 40 |
| `dep_fin_zero_elim` | 30 | 30 |
| `dep_ibval_bound` | 40 | 40 |
| `dep_vector_hd_cons` | 22 | 22 |
| `dep_reflect_elim` | 0 | 0 |
| `dep_reflect_intro` | 0 | 0 |

Across all candidate ATP successes absent from baseline there are 688 successful
attempts: 516 on common goals plus 172 from new fixtures.  600 reconstruct
(87.21%), essentially equal to candidate overall reconstruction (87.30%).  On
common goals alone, 428/516 reconstruct (82.95%); all 172 new-fixture successes
reconstruct.  At unique-goal level, 9/12 newly solved goals reconstruct by at
least one cell (4/7 old-goal gains and 5/5 new-fixture gains).

Inspection of the actual reconstruction outputs finds 52/600 successful new
attempts using a `dep: on` tacbest variant.  Twelve are common-goal gains; forty
are all 40 `dep_cast_refl` proofs.  Examples include
`CoLoR.Util.Vector.VecUtil.Vadd_cons` reconstructed by
`sauto lq: on dep: on`, and `dep_cast_refl` reconstructed by
`hauto lq: on dep: on`.  The remaining 548 use existing variants such as
`eauto`, `hauto`, or `qauto`.  Thus the new dependent reconstruction variants
are exercised and useful, while the measured gain is not an artifact of one
unreconstructable ATP family.

### Recommendation and owner decision

Recommendation: retain the current defaults (`opt_prop_case_erasure=true`,
`opt_erasure_guards=false`, `opt_refinement_types=true`,
`opt_refinement_decl_skips=true`, indexed families enabled, and rigid-clash
pruning enabled).  Screening gives direct positive evidence for Prop erasure,
unguarded transport, refinement, and declaration skips; indexed families incur
only modest formula cost and solve five of the seven new regression fixtures;
pruning is performance-neutral and slightly reduces high-premise formulas.
There is no evidence for adding the more aggressive CEnum declaration skips.

Owner decision required: accept the small full-grid old-goal regression (net -4
of 6,914 common goals and -0.108 ATP percentage points on common attempts) in
exchange for the indexed-family coverage and clean consistency grid, or request
a focused follow-up on the Z3/large-premise losses before integration.  Turning
indexed families off is not recommended as a default response: it lost one
screening ATP attempt, did not gain a screening goal, and does not isolate the
other translation changes between baseline and candidate.  TASK_10 itself made no default change.  The landing workflow, rather than this
evaluation record, owns any `PROGRESS` update, merge, commit, or port.

Final verification after restoring the measured-hit harness fix:
`bash eval/tests/test_grid_engine.sh` and `just check` both pass.
