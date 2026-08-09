# Sledgehammer premise selection: MePo, MaSh, MeSh, and definitional facts

*Research report, 2026-07-18, for `notes/premises.md` (bounded inclusion of
definitions of constants occurring in the goal and hypotheses). Sources:
`sledgehammer_mepo.ML`, `sledgehammer_fact.ML`, `sledgehammer_mash.ML`,
`sledgehammer.ML`, `sledgehammer_prover.ML`, `sledgehammer_atp_systems.ML`,
`sledgehammer_prover_smt.ML`/`smt_systems.ML`, `atp_problem_generate.ML`,
`atp_problem.ML` (all from `isabelle-prover/mirror-isabelle` master, July
2026; plus the Isabelle2012 `sledgehammer_filter.ML` for historical
comparison); Meng & Paulson 2009
(`notes/papers/meng-paulson-2009-lightweight-relevance-filtering-jal.txt`);
MaSh ITP 2013
(`notes/papers/kuhlwein-blanchette-kaliszyk-urban-2013-mash-itp.txt`); the
JAR 2016 fact selector
(`notes/papers/blanchette-greenaway-kaliszyk-kuhlwein-urban-2016-fact-selector-jar.txt`);
the Sledgehammer user manual
(`notes/papers/blanchette-sledgehammer-users-guide.txt`). Companion reports:
`premise-selection-coqhammer-dataflow.md`, `premise-selection-leanhammer.md`,
`premise-selection-literature.md`.*

## 1. MePo — the paper (Meng & Paulson 2009)

**Core algorithm (paper §4.2–4.3).** Maintain a pool of *relevant functions*
(symbols), seeded with the conjecture's symbols (function+type pairs —
overloading is disambiguated by requiring type match). Iterate: a clause
mentioning n functions, m of them relevant, scores m/n; accepted if score >
pass mark p; on acceptance all its functions become relevant. Pass mark
increases each iteration: **p' = p + (1−p)/c** (c = convergence parameter).
Terminates when no new clauses accepted. Empirically best: **p = 0.6,
c = 2.4** (tested c ∈ {1.6, 2.4, 3.2}; Vampire success peaked sharply at
p = 0.6, average problem shrank from 909 to 142 clauses).

**Frequency weighting (§4.4).** In the quotient, relevant symbols'
contribution m is boosted by rarity; the denominator counts irrelevant
functions unweighted (deliberately — weighting the denominator would
over-admit clauses with Skolem functions, each of which is rare). Score =
M/(M + |IR|) where M = Σ_{F∈relevant∩clause} freq_weight(F), and
**freq_weight(n) = 1 + 2/log(n+1)** (n = occurrences of the symbol in the
whole axiom set). Gentler decays like 1 + 1.4/log(log(n+2)) also worked;
1 + 1/√n penalized common functions too much.

**Definitions — the paper's answer (§4.5, "Other Refinements", exact
text):** "*Definition expansion is another refinement. If a function f is
relevant, and a unit clause such as f(X) = t is available, then it can be
regarded as relevant. To avoid including 'definitions' like 0 = N × 0, we
check that the variables of the right-hand side are a subset of those of the
left-hand side. Definition expansion is beneficial, but its effect is
small.*" I.e. the paper *did* experiment with force-treating definitional
unit equations of relevant constants as relevant (with an orientation sanity
check), found it beneficial but marginal. Also §4.5: simple-unit-clause
force-inclusion was tried and **abandoned** (100+ units hurt the search
space); a whitelist of force-included theorems existed but contained exactly
**one** theorem (about ⊆); plus a manual blacklist of 117 HOL theorems.

## 2. MePo — current implementation (`src/HOL/Tools/Sledgehammer/sledgehammer_mepo.ML`)

**Thresholds/decay.** `fact_thresholds = (0.45, 0.85)` by default
(`sledgehammer_commands.ML` line 67; manual §7.2: first threshold for first
iteration, second for the last, "quadratically interpolated" between). In
`mepo_suggested_facts`:
`decay = ((1 − thres1)/(1 − thres0))^(1/(max_facts+1))`; after accepting
facts in an iteration, `thres := 1 − (1 − thres) * decay^(#accepts)` — i.e.
threshold tightening is per-accepted-fact, geometric in the (1−thres) gap,
calibrated so the threshold reaches thres1 as the fact bound fills. Escape
hatch: if the *first* iteration accepts nothing and thres ≥
`ridiculous_threshold = 0.1`, retry with `thres / threshold_divisor` (=2.0).
`thres1 < 0` ⇒ take everything; `thres0 > 1` ⇒ take nothing.

**Scoring.** Per fact: partition its constants into rel/irrel against the
current relevant-constant table; score =
`rel_weight / (rel_weight + irrel_weight)`; a fact with no relevant
constants scores 0.
- `rel_weight_for _ freq = 1.0 + 2.0/ln(freq+1)` (the paper's formula,
  natural log).
- Irrelevant constants: `irrel_weight_for`: if freq < ⌈worse_irrel_freq⌉
  (=100) then `ln(freq+1)/ln 100` else
  `rel_weight_for freq / rel_weight_for 100`; multiplied by
  `higher_order_irrel_weight^(order−1)` (=1.05; higher-order constants
  penalized). Comment: both very rare and very common irrelevant constants
  get low penalties (rare can't pull in much; common are uninformative).
- `irrel_weight` starts at **−stature_bonus** (bonuses reduce the penalty
  side), then adds the irrel constants' weights.

**Fudge record (`default_relevance_fudge`, all values):**
`local_const_multiplier = 1.5` (constants whose name has no "." — i.e.
local/free constants — weigh 1.5×), `worse_irrel_freq = 100.0`,
`higher_order_irrel_weight = 1.05`, `abs_rel_weight = 0.5`,
`abs_irrel_weight = 2.0` (a pseudo-constant `Sledgehammer.abs` is added for
λ-abstractions — facts containing lambdas are penalized),
`theory_const_rel_weight = 0.5`, `theory_const_irrel_weight = 0.25` (a
pseudo-constant "ThyName. 1" is injected into every fact and the goal so
same-theory facts get a mild affinity),
`chained_const_irrel_weight = 0.25` (constants occurring in chained facts
have their irrelevance penalty quartered), `intro_bonus = 0.15`,
`elim_bonus = 0.15`, `simp_bonus = 0.15`, `local_bonus = 0.55`,
`assum_bonus = 1.05`, `chained_bonus = 1.5`, `max_imperfect = 11.5`,
`max_imperfect_exp = 1.0`, `threshold_divisor = 2.0`,
`ridiculous_threshold = 0.1`.

**`stature_bonus`** (status matched before scope): `(_, Intro) → 0.15`,
`(_, Elim) → 0.15`, `(_, Simp) → 0.15`, `(Local, _) → 0.55`,
`(Assum, _) → 1.05`, `(Chained, _) → 1.5`, everything else **0.0**.
**Crucially: statuses `Non_Rec_Def` and `Rec_Def` get NO bonus.** There is
no `def_bonus` in the fudge record, and none existed in Isabelle2012's
`sledgehammer_filter.ML` either (same stature_bonus cases; the 2012 fudge
additionally had `skolem_irrel_weight`). So **modern MePo does not give
definitional facts any rank boost and has no definition-expansion step** —
the paper's §4.5 def-expansion did not survive into the current MePo.
Definitional *status* matters elsewhere (translation & fact classification,
see §3/§5). Note that since bonuses subtract from irrel_weight,
chained/assum facts easily get score > 1 ("perfect"), making them
near-guaranteed picks; the JAR-2016 paper's prose summary (§2) is: "Chained
facts … take absolute priority; local facts are preferred to global
(top-level) ones; first-order facts are preferred to higher-order ones; rare
symbols are weighted more heavily than common ones."

**Per-iteration acceptance/bound.** `take_most_relevant`: sort candidates by
weight; all with weight > 0.99999 are "perfect" and always accepted; at most
`⌈max_imperfect^((remaining_max/max_facts)^max_imperfect_exp)⌉` imperfect
ones accepted per iteration (≈11 early, shrinking toward 1 as the budget
fills); then truncated to `remaining_max`. Rejected facts whose constant-set
intersects newly-relevant constants get their cached weight invalidated
("dirty") and are re-scored next iteration; at iteration 5
(`really_hopeless_get_kicked_out_iter`), hopeless facts with weight < 0.001
are dropped for good. Recursion stops when `remaining_max = 0` or nothing
new is accepted. So the **fact bound (`max_facts`) is enforced exactly** —
the filter returns ≤ max_facts facts, ordered by acceptance (≈ decreasing
relevance).

**Goal seeding.** `goal_const_tab` = constants of hyp_ts + concl_t
(+ theory pseudo-const); if empty, fall back to the chained facts'
constants; if still empty, successively fall back to constants of all
Chained, then Assum, then Local facts (`if_empty_replace_with_scope`).

**Special facts / reserved slots.** `insert_special_facts`: `ext` is added
if arity analysis suggests it could help (`could_benefit_from_ext`), and
`Collect_mem_eq`, `mem_Collect_eq`, `Collect_cong` are added whenever
`Collect`/`Set.member` occur anywhere (these two set constants are *ignored*
during scoring — treated as built-in — "Set constants tend to pull in too
many irrelevant facts", with their axiomatization appended instead). These
are **inserted at fixed index `special_fact_index = 45`** (comment: "High
enough so that it isn't wrongly considered as very relevant (e.g., for E
weights), but low enough so that it is unlikely to be truncated away if few
facts are included") and the list re-truncated to max_facts — genuine
reserved slots, not rank boosts. Fact order matters downstream because some
ATPs (E) weight facts by their rank (a `rank` is emitted per fact in the
TPTP `isabelle_info`).

## 3. Fact pool (`sledgehammer_fact.ML`) — are definitions in the pool?

**Yes — definitional equations are ordinary pool facts.** `all_facts`
sweeps all named global facts + named/unnamed local facts. `f_def` (from
`definition`), `f.simps` (from `fun`/`primrec`), inductive intro rules,
etc. are just facts. What Sledgehammer adds is a **status classification**
(`clasimpset_rule_table_of`): from `Spec_Rules.get` all equational spec
rules are partitioned by `is_rec_def` (RHS mentions the LHS head) into
`Rec_Def` and `Non_Rec_Def` statuses; simpset members get `Simp`, claset
intros `Intro`, (co)inductive spec intros `Inductive`. Statures are pairs
(scope, status) with scope ∈ {Global, Local, Assum, Chained}.

**Filtering that specifically hits definitions:** `is_package_def` rejects
package-generated defs by name suffix (`_case_def`, `_rec_def`, `_size_def`,
`_size_overloaded_def` with qualified names); `multi_base_blacklist` rejects
`.defs`, `.select_defs`, `.update_defs`, `eq.simps`, etc.; `no_atp`-declared
facts are excluded; tautology/technical/too-complex (apply depth > 18) facts
dropped. In 2012 `Bit0_def`/`Bit1_def` were excluded as `risky_defs` from
def-status classification.

**Does translation unfold definitions instead of passing them as axioms?**
Selected def-equations are passed **as axioms/formulas, never unfolded into
the goal**. Nuances: (a) Isabelle `abbreviation`s never reach Sledgehammer
at all (expanded at parse time, no constant, no fact). (b) `Let`
(goal-level `let`) is unfolded during pre-simplification (`presimp_prop` →
`Meson.presimplify` with `let_simps = true`) unless the target format
supports native FOOL `$let`; similarly `If` with `if_simps`. (c) The
λ-lifting translation *creates* fresh definitional equations (status
`(Global, Non_Rec_Def)`, `lam_fact_prefix`) for lifted lambdas — so
translation introduces defs, it doesn't eliminate them.
(d) `atp_problem_generate.ML` `pull_and_reorder_definitions` moves formulas
with TPTP role `Definition` to the front, topologically ordered by
RHS-constant dependency (currently near-vestigial for facts, which all get
role `Axiom`; in Isabelle2012 the status was exported as
`isabelle_info defN`). (e) The definitional statuses ARE exported to provers
that opt in (`generate_isabelle_info = true`: SPASS and one Zipperposition
config): `atp_problem.ML` DFG output appends `:lt` to a top-level equation
whose status is `non_rec_def` (orient left-to-right as rewrite) and `:lr`
for `simp`/`rec_def` statuses — i.e. **definitional facts get special
*prover-side* treatment (term ordering hints), not selection-side boosts.**

**Local `define`/chained facts:** a local `define x where "x = t"` produces
a Local-scope fact — ranked normally, with `local_bonus = 0.55` (and the
×1.5 local-const multiplier for its constants). Chained facts (`using …`)
are pool facts with Chained scope: MePo `chained_bonus = 1.5` (effectively
always selected but *not* formally force-included); MaSh gives unknown
chained facts a 0.9-weight component (§4); also the goal's hypotheses that
literally duplicate selected facts are replaced by `True` in translation.
Explicit user overrides: `sledgehammer (add: thms)` facts are
force-included — `add_and_take` puts them at the head and truncates the rest
to max_facts (manual: "The specified facts then replace the least relevant
facts that would otherwise be included"); `only:` restricts the pool to the
given facts. Induction rules are by default **excluded** wholesale after
selection (`induction_rules` defaults to Exclude; optionally
`instantiate_inducts` replaces them by goal-instantiated versions).

## 4. MaSh and MeSh (`sledgehammer_mash.ML`, ITP 2013, JAR 2016)

**Features:** term features = constant names (depth-≤2 patterns like
`map(rev)` built by `pattify_term`, `term_max_depth = 2`, breadth ≤
`max_pat_breadth = 5`), type constructors/patterns (`type_max_depth = 1`),
sort/class features, fixed-variable features, a theory-name feature, and a
`local` feature for non-global facts. Feature weights use IDF (JAR §3.5:
weight of feature f = ln(|Φ|/|{φ : f ∈ φ}|)). Learning: naive Bayes + kNN
over fact→dependency data from proof terms; proofs with > 20 dependencies
discarded (`max_dependencies = 20`; "decision procedure at work").

**Goal-feature enrichment:** features of chained facts are added at factor
`chained_feature_factor = 0.5`; features of up to
`num_extra_feature_facts = 10` most recent same-theory facts at factor
`extra_feature_factor = 0.1` (JAR §4.1: "Humans tend to group related
lemmas together").

**Fresh/unseen facts — the key mechanism (`find_mash_suggestions`):** facts
not in the learned "visibility graph" are `raw_unknown`. The MaSh-side
result is itself a 3-component mesh:
- weight **0.9**: unknown ∩ chained (each scored 1.0);
- weight **0.4**: unknown ∩ `proximate` (the `max_proximity_facts = 100`
  most recently defined facts), scored by
  `smooth_weight_of_fact rank = 1.3^(15.5 − 0.2·rank) + 15.0`;
- weight **0.1**: the raw learner ranking, scored
  `steep_weight_of_fact rank = 0.62^(log₂(rank+1))`, with the remaining
  unknowns attached as this component's "unks".

So **a constant defined a second ago: its `_def`/`.simps` facts have no
proof history, but they are within the last-100 proximity window
(weight 0.4·smooth) and, if chained, weight 0.9** — this is precisely how
MaSh avoids starving fresh definitions. JAR §4.2 states the motivation:
"MaSh may not be aware of all the available facts. In particular, it will be
oblivious to the very latest facts, introduced after Sledgehammer was
invoked for the last time, and these are likely to be crucial for the
proof." (ITP13 §4.3 nearly identically; papers give MaSh:proximity =
0.8:0.2 — the current code's 0.1/0.4/0.9 is the evolved version.)
Additionally, before querying, if ≤ `max_facts_to_learn_before_query = 100`
new facts exist, they are learned synchronously right then; more than that
triggers background learning.

**MeSh combination (`relevant_facts` + `mesh_facts`):** MePo and MaSh each
produce a ranked list, converted to scores by `steep_weight_of_fact` (the
Fig. 1(a) probability curve: "the first suggestion … about 15 times more
likely to appear in a successful proof than the 50th"), with global weights
`mepo_weight = 0.5`, `mash_weight = 0.5`. `mesh_facts`: normalize each
component's scores by the mean of its top-max_facts scores; a fact's
combined score = average over components of (global_weight × normalized
score at its rank), where a component that *doesn't know* the fact (it's in
that component's "unks" — e.g. facts MaSh never saw) contributes **NONE
(abstains)** rather than 0, while a fact the component knows but ranked
outside its list contributes 0.0. Union of top-max_facts of all components,
sorted, truncated to max_facts. **So yes: a principal stated benefit of
MeSh is that MePo covers facts MaSh has never seen used — and mechanically,
unseen facts are scored by MePo alone (abstention, not penalty, from
MaSh).** MaSh is asked for `2·max_facts + 25` suggestions
(`generous_max_suggestions`) to survive dedup. Default
`fact_filter = smart` ⇒ mesh if MaSh is enabled & trained, else pure MePo.

## 5. Bounds: how the count stays bounded

- **Hard per-invocation cap:** selectors are run once with `max_max_facts`
  = max over all scheduled slices' fact counts (×51/50 slack for later
  induction-rule filtering) (`sledgehammer.ML get_factss`); MePo's iteration
  enforces its bound exactly (§2 above); `take max_facts` everywhere after
  merging.
- **Slices (`good_slices`, per prover; `base_slice = (slice_size, abduce,
  falsify, max_facts, fact_filter)`):** each prover invocation is a slice
  with its *own* fact count and fact filter, "found empirically". Examples
  (master): **E**: 128/1024/128/2048/512/1024/64/512/32/2048/256/512/1024/
  16/512/64/128/2048/128/2048 — all mesh; **Vampire**: 512/2048/128/1024/
  256/1024/256/2048/256/512/2048/64/256/256/256/32/512/512/1024 — all mesh;
  **iProver**: 32 mesh, 512 mesh, 128 **mash**, 1024 mesh, 256 **mepo**;
  **SPASS**: 150/500/50/250/**1000 mepo**/150/300/100 (mesh except one
  mepo); **Zipperposition**: 512 mesh + 512 **mepo** (its mepo slice passes
  `--sine=50` — prover-side SInE on top!); **cvc5/CVC4/veriT (SMT)**:
  512/64/1024/32/128/256 all mesh; agsyHOL 60, alt-ergo 100, LEO-II 40,
  Leo-III 512, Satallax 256. Slice fact list = prefix of the corresponding
  filter's ranked list (`facts_of_basic_slice`:
  `goal_facts @ take num_facts nongoal_facts`). When the user pins
  `fact_filter`, slices are "triplicated" across filters; `max_facts` (user)
  overrides per-slice counts (min). Manual: default `slices` = 24 × #cores;
  `max_facts` default "smart" = per-slice values, "typical values lie
  between 0 and 1000".
- **Reserved slots vs boosts — summary:** true reserved slots exist only
  for (a) user `add:` facts (head of list), (b) the goal-as-fact entries,
  (c) MePo's special facts at index 45 (`ext`, set-comprehension axioms).
  Chained/local/assumption facts and def/simp/intro/elim statuses are
  handled by *score* bonuses only (chained's 1.5 bonus is de-facto
  inclusion). MaSh side: chained-unknown 0.9 / proximate-unknown 0.4
  components are score-based too, and `mesh_facts`' single-component form
  backfills leftover slots with unknown facts
  (`take (max_facts − length sels) unks`) — i.e. when MaSh alone runs,
  fresh facts fill the tail.

## Direct answers to the headline design question

Sledgehammer does *not* force-include definitions of goal constants. Its
answers to "goal mentions f, get f's definition in" are:

1. MePo's seeding makes any fact whose symbols are ⊆ goal symbols score 1.0
   ("perfect", always accepted before the imperfect quota) — a
   non-recursive `f_def`/`f.simps` whose RHS uses only
   common-but-goal-relevant symbols typically passes early, and rare-symbol
   weighting (1 + 2/ln(freq+1)) makes an equation about a rare goal
   constant score high even with some junk symbols.
2. The paper's explicit "definition expansion" (force-relevance of oriented
   unit def-equations of relevant constants, var(rhs) ⊆ var(lhs)) was
   validated as "beneficial but small" and is *not* in the current code.
3. Freshly defined constants are covered not by MePo but by MaSh's
   proximity component (last-100 facts, weight 0.4) and chained component
   (0.9), and by MeSh's abstention semantics letting MePo alone rank
   history-less facts.
4. Definitional status is exploited *after* selection as prover hints
   (SPASS `:lt` rewrite orientation) and by lambda-lifting emitting defs.
5. All bounding is a single ranked list truncated per slice at empirically
   tuned sizes (16–2048), with reserved slots only for user-added facts and
   MePo's 3-4 special facts at index 45.
