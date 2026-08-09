# CoqHammer premise-selection dataflow: definitions of goal/hypothesis constants

*Research report, 2026-07-18, for `notes/premises.md` (bounded inclusion of
definitions of constants occurring in the goal and hypotheses). Sources: the
`extraction` branch working tree (all paths under
`/home/dev/coqhammer/worktrees/extraction`, all under `src/plugin/` unless
noted). Companion reports: `premise-selection-sledgehammer.md`,
`premise-selection-leanhammer.md`, `premise-selection-literature.md`.*

# 1. `hhdef` — what's available at selection time

`src/plugin/hh_term.ml:5-10`:
```ocaml
type hhdef =
  hhterm (* "name" term *) *
    bool (* is opaque? *) *
    hhterm (* kind; Comb(Id "$Sort", Id "$Prop") if type is a proposition *) *
    hhterm Lazy.t (* type *) *
    hhterm Lazy.t (* term: definiens (value or proof term) *)
```
The definiens IS present (lazily). Built in `src/plugin/hammer_main.ml:149-177`
(`hhdef_of_global`): for `ConstRef c` the body is `lazy (hhproof_of c)` (line
165-167); `hhproof_of` (136-147) returns `hhterm_of body` or `Id "$Axiom"`
when the body is inaccessible (opaque table not loaded, issue #86). For
Ind/Construct/Var the term slot is always `Id "$Axiom"`. Opaque constants keep
their real body in the hhdef term slot (`hhproof_of` uses
`Utils.body_of_constant`, which does return opaque bodies) — but
`Coq_convert.to_coqdef` (`src/plugin/coq_convert.ml:248-262`) discards the
body when `opaque=true`, mapping the constant to `Const(name)` (so opaque
proofs are never unfolded in translation). So **"size of definition" is
computable at selection time** (force the lazy term and count nodes), with the
caveats: forcing is what `get_deps` already does anyway, and Prop-sorted
constants get `(name, Const(name), ty, SortProp)` (`coq_convert.ml:245-247`),
i.e. their bodies are irrelevant to translation.

`coqdef` (translation-level): `src/plugin/coqterms.ml:41-42`:
`string (name) * coqterm (value) * coqterm (type) * coqterm (sort)`.

# 2. features.ml — feature/dep extraction and the predictor protocol

## Feature terms
- `get_def_fea_term` (`features.ml:123-128`): opaque def → type only;
  transparent def → `Comb(ty, body)` (type AND body features).
- `extract_features` (`features.ml:56-121`): walks the hhterm, collecting for
  each non-logical Const/Ind/Construct `c`: the plain name `c`, a
  polarity-tagged `c+`/`c-` (`opt_feature_polarity = true`, line 8), and for
  applications a head-arg pair feature `c ^ "-" ^ top_feature(arg)` (lines
  102-117, e.g. `add-X`, `cons-nat`). Polarity flips under Prod domains,
  `not`, `iff` (both), `all` domain (lines 73-93). Logical constants
  (`Corelib.Init.Logic.*` prefix, lines 22-27) are skipped as features.
- `get_def_features` (130-131), cached at 157-167 keyed on name
  (`features_cache`, 147); vars never cached (154-155).

## Goal features include hypotheses — YES
`get_goal_features` (`features.ml:133-140`):
```ocaml
let get_goal_features (hyps : hhdef list) (goal : hhdef) : string list =
  let rec pom lst =
    match lst with
    | [] -> get_def_fea_term goal
    | h :: t ->
       Comb(Comb(Comb(Id "$Prod", Comb(Id "$Name", Id "$Anonymous")), get_def_fea_term h), pom t)
  in
  extract_features (pom hyps)
```
Hypotheses are wrapped as Prod domains around the goal, so hyp constants
contribute features (with flipped polarity, as antecedents). This is the ONLY
channel by which hyp constants influence selection in the main path — nothing
forces their definitions into the premise list (that was exactly d4b6a40's
revert; see §7).

## Dependencies
`get_deps` (`features.ml:142-145`):
```ocaml
let get_deps (def : hhdef) : string list =
  match def with
  | (_, _, _, ty, prf) ->
    extract_consts (Comb(Lazy.force ty, Lazy.force prf))
```
`extract_consts` (29-45) collects all Const/Ind/Construct names (excluding
logic names) from type+body — one level, no transitive closure. Cached in
`deps_cache` (169-179).

## `is_nontrivial` (181-187)
Filters defs with empty name, logic-prefix names, and (option-controlled)
`Stdlib.Program.*`, `Stdlib.Classes.*`, `Stdlib.Logic.Hurkens.*`
(`Opt.filter_program/filter_classes/filter_hurkens`, default all `true`,
`opt.ml:319-353`).

## `extract` (189-224) — predictor input files
For each nontrivial def, in `get_defs` order:
- `<f>seq`: one def name per line (theorem order).
- `<f>fea`: `name:"fea1", "fea2", ...`.
- `<f>dep`: `name:dep1 dep2 ...` where deps are filtered to names present in
  the (filtered) defs set (line 209:
  `List.filter (fun a -> StringSet.mem a names) pre_deps`).
- `<f>conj`: a single line `"fea1", "fea2", ...` =
  `get_goal_features hyps goal`.

**The predictor gets NO dependency info for the goal — only its feature
vector.** Hyps and goal are never written to seq/dep/fea (they're not in
`defs`).

## `run_predict` (246-292)
```
predict <f>fea <f>dep <f>seq -n <pred_num> -p <pred_method> < <f>conj > out
```
(lines 248-251). Output: single line of space-separated names, parsed into a
StringSet, then
`List.filter (fun def -> StringSet.mem (get_hhdef_name def) predicts) defs`
(line 289) — so the result is exactly the predictor's top-N intersected with
defs, order lost (defs order kept).

## `predict` (299-307)
`extract` + `run_predict fname defs !Opt.predictions_num !Opt.predict_method`
+ `clean`. Post-d4b6a40 there is no unioning of direct deps.

## `choose_given_lemmas` (226-244) — the given-lemmas algorithm
```ocaml
let choose_given_lemmas (hyps : hhdef list) (defs : hhdef list) (lems : hhdef list) (goal : hhdef) : hhdef list =
  Msg.info "Choosing definitions...";
  let ndefs = List.filter is_nontrivial defs in
  ...
  let names = Hhlib.strset_from_lst (List.map get_hhdef_name ndefs) in
  let filter_deps deps = List.filter (fun a -> Hhlib.StringSet.mem a names) deps in
  let choose_def def =
    get_hhdef_name def :: filter_deps (get_deps_cached def)
  in
  (* The goal and the hypotheses are local to the current proof, so
     their dependencies must not be cached under their names. *)
  let goal_deps = filter_deps (get_deps goal) in
  let hyps_deps = List.concat (List.map (fun h -> filter_deps (get_deps h)) hyps) in
  let objs =
    Hhlib.strset_from_lst
      (goal_deps @ hyps_deps @ List.concat (List.map choose_def lems))
  in
  List.filter (fun def -> Hhlib.StringSet.mem (get_hhdef_name def) objs) defs
```
Exact algorithm: premises = {each lemma} ∪ {direct deps of each lemma} ∪
{direct deps of goal} ∪ {direct deps of each hypothesis}, all restricted to
nontrivial accessible defs. **Bounds: none** — depth-1 only (no closure), but
no cardinality cap. mli comment `features.mli:13-17` confirms the contract.
This IS the "definitions directly referenced by goal/hyps/lemmas" mechanism,
but only on the `hammer_deps`/given-lemmas path.

# 3. hammer_main.ml — assembly and control flow

- Goal hhdef: `get_goal` (205-210), name `_HAMMER_GOAL`, opaque, kind Prop,
  type = conclusion, body = itself.
- Hyps: `get_hyps` (193-203) via `hhdef_of_hyp` (179-191): name = hyp id,
  transparent iff `LocalDef` (let-bound).
- Defs: `get_defs` (269-271) = `my_search` (223-252): all accessible globals,
  filtered by `Search.blacklist_filter` (if `Opt.search_blacklist`, default
  true, `opt.ml:355-365`) and by the `Hammer Filter` module table
  (`filter_modules`, 226-228; table at `opt.ml:379-396`), then typability
  check (244-251), deduped by name (`unique_hhdefs`, 254-267).
- Given lemmas: `get_given_lemmas` (273-286).

## Main path (`hammer_main_tac`, 910-985 → `do_predict`, 849-865)
GSMode (`Opt.gs_mode`, default **8**, `opt.ml:78-91`; `Set`→value,
`Unset`→16, 0 disables): one `Features.extract` (851), then per candidate
`fun () -> Features.run_predict fname deps preds_num pred_method` (857).
`run_gs_provers` (735-815) runs the first `gs_mode` still-enabled candidates
in parallel forks; each fork enables exactly one prover and calls
`Provers.predict deps1 hyps deps goal` (775). **The hypotheses-always-passed
comment is at hammer_main.ml:773-774**:
```ocaml
(* All hypotheses are always passed to the ATPs (only deps
   are subject to premise selection) *)
```
Reconstruction failure retries the next batch of candidates
(`attempt`/`retry_available`, 917-985).

`greedy_predictor_sequence` (817-840), exact (prover, method, count) ladder
in order: CVC4 nbayes-128; Vampire knn-1024; CVC4 knn-64; CVC4 knn-256;
Vampire nbayes-64; CVC4 nbayes-256; Eprover nbayes-64; Z3 nbayes-128; Vampire
knn-64; CVC4 nbayes-32; CVC4 nbayes-1024; Z3 nbayes-32; Vampire nbayes-128;
Eprover knn-128; Vampire nbayes-32; Z3 knn-64; Vampire knn-256; Eprover
nbayes-32; Z3 nbayes-64; CVC4 nbayes-64; Eprover nbayes-256; Vampire
nbayes-1024; Z3 nbayes-1024. (With default gs_mode=8 only the first 8 enabled
entries run initially.)

Non-GSMode (`gs_mode = 0`, 863-865): `Features.predict hyps deps goal` with
`Opt.predictions_num` (default **1024**, `Unset`→128, min clamp 16,
`opt.ml:3-16`) and `Opt.predict_method` (default `"knn"`; accepts
knn/nbayes/rforest, `opt.ml:153-169`); then
`Provers.predict deps1 hyps deps goal` with minimization
(`minimize_threshold` default 8, `opt.ml:63-76`).

## Given-lemmas path (`do_choice`, 867-891)
Appends requested lemmas missing from search results to `deps` (869-877),
calls `Features.choose_given_lemmas` **once**, then either runs 4 prover
candidates (GSMode) all sharing the same fixed `deps1` (879-889) or plain
`Provers.predict` (891). Empty lemma list allowed — then premises = direct
deps of goal/hyps only (comment at 944-947).

## Other Opt knobs (opt.ml)
`predictions_num` (3), `sauto_timelimit` (18), `atp_timelimit` (33, default
20), `reconstr_timelimit` (48), `minimize_threshold` (63), `gs_mode` (78),
per-prover enables (93-139), `predict_path` (141), `predict_method` (153),
`parallel_mode` (171), `debug_mode` (183),
`ClosureGuards`→`Coq_transl_opts.opt_closure_guards` (309-317), filters
(319-353), `search_blacklist` (355), `clear_unused` (367), `Hammer Filter`
module table (379-396). **No depth-limit / definition-size /
dependency-closure knob exists.**

# 4. src/predict — the C++ predictor

Built with `-DCOQ_MODE` (`Makefile.coq.plugin.local:7`). Input format
(`main.cpp:9-22`, `format.cpp`): `<syms> <deps> <seq>` files; `-n`
predictions; `-p` method; query features on stdin. `read_deps`
(`format.cpp:41-72`): in COQ_MODE all deps are kept (`format.cpp:62-63`),
otherwise only past deps (`d < th`). Query features not present in the
training symbol table are silently dropped (`parse_feature_list`,
`format.cpp:143-153`) — an unknown goal constant contributes nothing.
Interaction mode (`main.cpp:49-61`): `learn_all()` then predict per stdin
line; `learn_all` = `learn(0, syms.size()-1)` (`predictor.cpp:41-43` — note:
skips the last theorem).

## tf-idf (`tfidf.cpp:10-50`)
`get(s) = log(#theorems) − log(freq[s])` — standard idf; rare symbols weigh
more.

## kNN (`knn.cpp:30-93`) — confirmed: neighbors themselves are scored, and
their deps
Similarity: for each query symbol, each theorem containing it gains
`pow(tfidf_weight, 6)` (lines 40-46). Then adaptive-k loop (64-89):
```cpp
for (long k = 0; k < maxth && no_recommends < no_adv; ++k) {
    long nn = neighbours[k].first;
    double o = neighbours[k].second;
    if (ans[nn].second <= 0) { no_recommends++; ans[nn].second = age(k) + o; }
    else ans[nn].second += o;
    // dependencies of the neighbor also gain some relevance ...
    LVec ds = deps[nn];
    double ol = 2.7 * o / ds.size();
    for (const auto& d : ds) { ... ans[d].second = age(k) + ol; ... }
}
```
`age(k) = 500000000 - 100*k` (line 26-28) stratifies by k. So kNN recommends
**the neighbor theorem itself AND its recorded dependencies**. Since a
definition `f` whose unfolding is often needed appears as a *dep* of many
theorems, it can be recommended — but only if similar theorems exist in the
(current-session) corpus.

## Naive Bayes (`nbayes.cpp`) — confirmed self-dependency weight 1000
`learn` (97-100):
```cpp
void NaiveBayes::learn(const LVec& csyms, sample_t i, const LVec& cdeps) {
  add_sample_freqs(csyms, i, 1000);
  for (const auto d : cdeps) add_sample_freqs(csyms, d, 1);
}
```
Each fact is learned as its own dependency with weight 1000; each actual
dependency `d` gets the depending theorem's features with weight 1. Scoring
(59-84): `s = 30*log(tfreq[i])` + for each feature of theorems-depending-on-i:
matched query feature → `+ tfidf * log(5*sfreqv/n)`; unmatched →
`+ tfidf * 0.2 * log(1+(1-sfreqv)/n)` (note `1-sfreqv` ≤ 0 for sfreqv≥1:
penalty); query features absent from i's co-occurrence table →
`- tfidf*18` (line 81). Net effect: nbayes strongly favors facts whose own
feature vector overlaps the goal's, plus facts that are deps of
feature-similar facts.

# 5. coq_transl.ml — axiom emission for a problem

`write_problem` (`coq_transl.ml:2489-2503`): `get_axioms (goalname ::
depnames)`; TPTP written by `Tptp_out.write_fol_problem` with the goal axiom
as conjecture.

Caller `Provers.write_atp_file` (`provers.ml:406-417`):
```ocaml
let depnames = List.map Hh_term.get_hhdef_name (hyps @ deps1) in
...
Coq_transl.reinit (goal :: hyps @ deps);   (* deps = ALL accessible defs *)
Coq_transl.retranslate (name :: depnames);
Coq_transl.write_problem fname name depnames
```
So: `Defhash` (via `reinit`, `coq_transl.ml:66-95`, lazy conversion per def)
knows **every** accessible definition, but axioms are translated/emitted only
for goal + all hyps + selected `deps1`.

`get_axioms` (`coq_transl.ml:2465-2471`):
```ocaml
let get_axioms lst =
  let structural = List.concat (List.map Case_dependencies.find lst) in
  retranslate structural;
  coq_axioms @
    Hhlib.sort_uniq ... (List.concat (List.map Axhash.find (... (lst @ structural))))
```
`coq_axioms` (141-156): `_HAMMER_COQ_TRUE/FALSE/TYPE_TYPE` (+Set axioms
unless `opt_set_to_type`).

## `Case_dependencies` (200-209 + 1273-1281)
Recorded during translation of a def whenever an emitted case equation
matches on inductive `indname` (comment 1274-1276: "Every emitted case
equation relies on the structural theory of its scrutinee"), including via
hash-consed lifts (`Lift_dependencies`, 214-253). `get_axioms` then
**unconditionally** pulls the full translation of those *inductive type*
names for every selected premise's recorded scrutinee types — regardless of
selection. What that translation contains is the `IndType` branch of
`add_def_axioms` (2361-2406): for non-Prop inductives — injection axioms per
constructor (`add_injection_axioms`, 2183), pairwise discrimination axioms
(`add_discrim_axioms`, 2270), a typing axiom for the inductive
(`add_typing_axiom`, 2044), and inversion/exhaustiveness axioms
(`add_inversion_axioms`, 2328, if `opt_inversion_axioms`); for Prop-targeted
inductives — propositional inversion + typing. Note the closure is **one
level**: `structural` names are translated but their own Case_dependencies
are not chased from `get_axioms` (only `lst`'s are).

**Constructor axioms are NOT brought in by selecting an IndType**:
constructors are separate hhdefs with their own `translate` (typing axioms
via the `$Construct` case of `to_coqdef`/`add_def_axioms` non-IndType
branch); the IndType translation emits injection/discrim/inversion mentioning
constructors as raw constants, but a constructor's typing axiom appears only
if the constructor itself is a selected premise (or hyp/goal). Similarly
inversion axioms mention constructors without their typings.

## Unselected constants stay uninterpreted — confirmed
`translate name` (2443-2455) runs `add_def_axioms (Defhash.find name)` for
that one def; for a non-Prop constant it emits
`add_typing_axiom name ty >> add_def_eq_axiom def` (2418-2422); for a Prop
constant just the statement-as-axiom (2409-2417). `add_def_eq_axiom`
(2106-...) emits `$_def_<name>` unfolding equations (with lambda/fix/case
lifting producing auxiliary `$_def_...`/`$_case_...` axioms *within the same
translate*). Any constant `g` occurring in the body/type of a selected
premise is translated to the FOL constant/function symbol `g` with **no
axioms** unless `g` is itself in `lst` — the only exceptions are the
Case_dependencies structural closure above and the internal lifted
auxiliaries emitted as part of the owner's own axiom list.

# 6. How hypothesis constants are handled today (summary)

- Hyps are always sent to the ATP as axioms (`provers.ml:408` —
  `depnames = hyps @ deps1`; `hammer_main.ml:773-774` comment).
- Hyp constants DO contribute goal-query features (`get_goal_features`,
  features.ml:133-140).
- But on the main (Prediction) path, **nothing forces the definitions of
  goal/hyp constants into `deps1`**; a hyp `H : f x = g x` yields
  uninterpreted `f`, `g` unless the predictor happens to rank `f`/`g` in the
  top N (possible: constants ARE theorems in the corpus — every accessible
  def is a line in seq/fea/dep — and nbayes' 1000-weight self-learning +
  kNN's dep-boost make goal-feature-overlapping constants rankable, but with
  no guarantee).
- On the given-lemmas path (`Choice` mode, `do_choice` →
  `choose_given_lemmas`), depth-1 definitions of goal/hyp/lemma constants ARE
  included, uncapped.

# 7. History: d4b6a40 (committed 2026-07-18)

"Remove forced direct-dependency premises; restore predictor contract."
Removed from features.ml: `direct_goal_dependencies` (goal deps ∪ hyp deps,
filtered to nontrivial defs — same computation as in `choose_given_lemmas`)
and `add_direct_goal_dependencies` (union into every prediction result);
removed `greedy_selected_deps` from hammer_main.ml, which had applied the
union per GSMode candidate. Rationale in the message: uncapped union meant
"predict N" and GSMode per-candidate counts could return far more than N
premises, confounding evaluation against the baseline. Preceding relevant
history: `174a9dc` "hammer with given lemmas (#212)" introduced
`choose_given_lemmas`.

# Key design-relevant facts distilled

1. Selection granularity is the whole accessible-defs list; predictor is
   retrained from scratch per invocation from session-local seq/dep/fea
   files; goal is features-only to the predictor.
2. Definition bodies are available at selection time (lazy hhterm), so
   size-of-definition filtering is implementable in
   `features.ml`/`hammer_main.ml` without new plumbing; `get_deps_cached`
   already gives depth-1 constant sets cheaply.
3. `choose_given_lemmas` (features.ml:226-244) is the existing depth-1,
   uncapped template for "goal/hyp direct definitions"; the reverted
   `add_direct_goal_dependencies` was the same set unioned into predictions —
   the objection was violating the N bound, not the idea.
4. The translation already has one precedent for "unconditional semantic
   closure": `Case_dependencies` (coq_transl.ml:197-209, 2465-2467) delivers
   scrutinee inductives' structural theory outside premise selection; but
   constructor typing axioms are not part of it.
5. Counts requested from the predictor in GSMode are fixed per ladder entry
   (32/64/128/256/1024); any forced additions either break these budgets
   (d4b6a40's complaint) or must be carved out of N (e.g. request N−k
   predictions and reserve k for forced definitions, or cap forced defs by
   size/count).
