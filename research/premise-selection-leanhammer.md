# LeanHammer / lean-auto / Duper: handling of definitions in premise selection

*Research report, 2026-07-18, for `notes/premises.md` (bounded inclusion of
definitions of constants occurring in the goal and hypotheses). Sources: the
LeanHammer paper (arXiv:2506.07477,
`notes/papers/zhu-clune-avigad-jiang-welleck-2025-leanhammer-premise-selection-iclr.txt`),
the lean-auto paper (arXiv:2505.14929,
`notes/papers/qian-clune-barrett-avigad-2025-lean-auto-cav.txt`), the LeanDojo
paper (arXiv:2306.15626), and the GitHub repositories JOSHCLUNE/LeanHammer,
leanprover-community/lean-auto, leanprover-community/duper,
hanwenzhu/premise-selection, leanprover/lean4 (LibrarySuggestions). Companion
reports: `premise-selection-coqhammer-dataflow.md`,
`premise-selection-sledgehammer.md`, `premise-selection-literature.md`.*

## 1. LeanHammer paper — "Premise Selection for a Lean Hammer" (arXiv:2506.07477, Zhu, Clune, Avigad, Jiang, Welleck; v2 updated Feb 2026)

**Selector (LeanPremise, §3.3):** encoder-only transformer
(sentence-transformer family, small/medium/large; large = 82M params), dense
retrieval by cosine similarity between goal-state embedding and
premise-signature embeddings (Eq. 1). Trained with a *masked* contrastive
InfoNCE loss (Eq. 2, §3.3.1) that masks other-proofs' positives from the
negative set. States and signatures use "normalized serialization" (§3.2.1):
notation disabled, fully qualified names — deliberately syntax-independent.

**What counts as a premise (§3.2.1–3.2.2):** both **theorems and
definitions**. Extracted fields: docstring, kind (theorem/definition), name,
args, type. Training positives = theorems appearing in the proof term **plus
theorems and definitions explicitly used in `rw`/`simp` calls** — i.e.,
definitional/rewriting usage is captured in the training signal rather than
by a deterministic rule. A blacklist of 479 basic logic theorems filters
trivia.

**Premise counts (§4.1, §D.3, tuned on Mathlib-valid):** k₁ = 16 premises to
lean-auto (Aesop unsafe rule at 10% priority:
`(add unsafe 10% (by auto [*, <premises>]))`), k₂ = 32 premises as individual
premise-application Aesop rules (`add unsafe 20% <premise>`). Pipeline
variants: `aesop` / `auto` / `aesop+auto` / `full` (default) / `cumul`.
Mathlib-test proof rates (large model): 24.1 / 21.3 / 28.5 / 30.1 / 37.3%
(cumul).

**Deterministic additions after neural selection: none in the paper.** The
paper does not add definitions of goal constants, equation lemmas,
constructor/recursor facts, or simp sets post hoc; unfolding is delegated to
Aesop's default rule set and to how lean-auto/Duper elaborate whatever
premises arrive. The local context is always passed (`auto [*, ...]`).

**Fresh/user-defined constants (§3.3.2, "dynamic context adaptation"):**
client collects *all premises currently in the environment* (imported +
current file, incl. local lemmas), server caches embeddings for fixed Mathlib
versions and **embeds only the signatures of new premises uploaded by the
client on the fly**. So unseen premises are retrievable because retrieval is
over signature text, not a fixed vocabulary. Symbolic baseline: MePo; notably
LeanPremise ∪ MePo = 35.9% vs 30.1% alone (§4.3) — complementary.

## 2. LeanHammer frontend (github.com/JOSHCLUNE/LeanHammer)

Files: `Hammer/Tactic.lean`, `Hammer/HammerCore.lean`, `Hammer/Options.lean`.
Current version orchestrates **Duper, grind, Lean-SMT (cvc5), Aesop** in
parallel via `runAesopWithSubprocedures` (Aesop unsafe rules with priorities
`aesopPremisePriority=20`, `aesopDuperPriority=10`, `aesopGrindPriority=5`,
`aesopSmtPriority=10`).

- Syntax `hammer [facts] {options}`; premise budgets per solver:
  `aesopPremises=32`, `duperPremises=16`, `grindPremises=100`,
  `smtPremises=16`. Each solver gets `userInputTerms ++ premises.take k`.
- **Default selector** (`Hammer/Tactic.lean` line 23):
  `set_library_suggestions ... Cloud.premiseSelector <|> sineQuaNonSelector.intersperse currentFile`
  — i.e., neural cloud selector, **falling back** (on network failure) to
  SInE **interleaved 50/50 with a `currentFile` selector** that
  force-supplies theorems from the current file. That interleave is the
  explicit "constants/lemmas too fresh for the server" mitigation at the
  symbolic-fallback level.
- **Deterministic filters, not additions:** `autoPremiseEligible` drops
  premises whose types contain embedded proof terms (unsound for lean-auto's
  HOL translation); `grindPremiseEligible` checks
  `Grind.mkEMatchTheoremForDecl` compatibility.
- **Preprocessing option**
  `preprocessing ∈ {aesop, simp_target, simp_all, no_preprocessing}` — a
  `simp`-set argument may be passed (`hammer [...] simp lemmas`), used only
  in the simp preprocessing call, not forwarded to ATPs.
- Duper path (`HammerCore.lean` ~113–158): negates goal via
  `Classical.byContradiction`, collects formulas with
  **`Duper.collectAssumptions`** (not `Auto.collectAllLemmas` — comment: the
  latter has no "ignore unusable facts" mode), applies
  `Auto.unfoldConstAndPreprocessLemma #[]` (**empty unfold list** — no
  unfolding in the hammer path, only β/reduction preprocessing needed by
  monomorphization), gets Zipperposition unsat core via `runAutoGetHints`,
  reconstructs with Duper on the core
  (`duper [*, coreFacts] {preprocessing := full}`).

**Key implicit mechanism:** because the neural selector may return a
*definition* name, and hammer routes premises through **Duper's `elabFact`**,
definitions among the selected premises get expanded into their equational
lemmas automatically (see §3 below). So "definition handling" in LeanHammer =
(a) selector is trained to propose definitions used in `rw`/`simp`, (b) fact
elaboration turns any selected definition into equations. There is **no**
rule "for every constant in the goal, add its definition".

## 3. Duper (leanprover-community/duper, `Duper/Tactic.lean`)

- `duper [facts] {options}`; **no automatic hypothesis inclusion** — `duper`
  = `duper []`; `*` adds the local context.
- **Definitional unfolding: yes, per supplied fact.** `elabFact` (line ~68)
  case-splits on the constant kind:
  - `.defnInfo`: adds the definition itself (if a Prop) **and** all equations
    from `getEqnsFor?` (Lean's equation-lemma generator, handles
    `match`/structural/well-founded recursion) — lines 86–98.
  - `.recInfo`: `addRecAsFact` generates one definitional equation per
    constructor by `reduceRecMatcher?` + `Eq.refl` (recursor ι-reduction
    equations).
  - Theorems/axioms/fvars: taken as-is.
- No global unfolding of constants it merely *encounters* — expansion happens
  only for facts explicitly passed. Options: `portfolioMode` (default true,
  3–4 self-instances), `portfolioInstance` 0–24,
  `preprocessing ∈ {full, monomorphization, no_preprocessing}`,
  `inhabitationReasoning`, `includeExpensiveRules`.

## 4. lean-auto (leanprover-community/lean-auto; paper arXiv:2505.14929, CAV 2025, Qian, Clune, Barrett, Avigad)

Syntax: `auto [<terms>,*] u[<idents>,*] d[<idents>,*]`.

- **`d[g₁,…,gₙ]`** — "collect all definitional equalities associated with
  gᵢ" (paper §7.0.1). Implementation `Prep.elabDefEq`
  (`Auto/Translation/Preprocessing.lean` line 56): for `defnInfo` uses
  **`getEqnsFor?`** (same Lean equation lemmas as Duper); for `recInfo` uses
  `addRecAsLemma` (per-constructor ι-equations via `reduceRecMatcher?`);
  axioms/theorems/ctors → nothing; opaque/quot/inductive → error.
- **`u[f₁,…,fₙ]`** — recursive **syntactic unfolding**: `getConstUnfoldInfo`
  grabs `ci.value?` (fails if not a definition), `topoSortUnfolds`
  topologically sorts so later names don't occur in earlier bodies, **errors
  on cyclic dependency** (this is the termination bound — no depth cutoff,
  recursion simply can't be unfolded this way; recursive functions must go
  through `d[...]` equations instead). `unfoldConsts` then substitutes bodies
  into every lemma via `unfoldConstAndPreprocessLemma` (+ `prepReduceExpr`,
  `Core.betaReduce`).
- **Both are strictly user-driven.** `collectAllLemmas` (`Auto/Tactic.lean`)
  gathers: local ctx (`collectLctxLemmas`, automatic), user terms
  (`collectUserLemmas`), lemma DBs (`collectHintDBLemmas`, `* <dbname>`),
  defeqs (`collectDefeqLemmas` from `d[]`). lean-auto does **not** auto-add
  `f.def`/equations for constants met during monomorphization/translation;
  untranslated constants become uninterpreted HOL symbols. Paper §4.3.3: it
  "can be *configured* to collect these equational theorems".
- Paper §7.0.1 preprocessing also generates equational theorems between
  "maximal subexpressions not containing logical symbols" (abstraction-level
  equations), and §7.0.2 collects constructor/recursor facts for
  inductive-type instances found during monomorphization — the one place
  where inductive-structure facts *are* added automatically, driven by the
  instances the monomorphizer encounters, not by an unbounded closure.
- Pipeline: CIC → COC → monomorphization → λ^{c.u.} HOL → TPTP
  (Zipperposition, `auto.tptp.solver.name`) / SMT; options
  `auto.mono.ignoreNonQuasiHigherOrder`, etc.

## 5. Lean core `Lean.LibrarySuggestions` (leanprover/lean4 `src/Lean/LibrarySuggestions/*.lean`, 2025, Kim Morrison) — the symbolic ecosystem LeanHammer plugs into

- `Selector : MVarId → Config → MetaM (Array Suggestion)`;
  `Config.maxSuggestions` (default 100), `caller`, `filter`;
  `Suggestion = {name, score, flag}`. Registered via
  `set_library_suggestions` / `@[library_suggestions]`.
- **Goal symbols:** `MVarId.getRelevantConstants` = constants of goal type ∪
  all hypothesis types, **skipping instance arguments and proof subterms**
  (`Expr.relevantConstants`). This is their canonical "constants occurring in
  goal+hyps" extraction.
- **`mepoSelector (useRarity) (p := 0.6) (c := 2.4)`** (`MePo.lean`):
  Meng–Paulson relevance filter; iterates threshold `p ← p + (1-p)/c`, score
  = M/(M+R′) with optional rarity weight `1 + 2/(log₂ freq + 1)`; candidates
  restricted to `wasOriginallyTheorem` and not `isDeniedPremise` —
  **theorems only, definitions never selected**.
- **`sineQuaNonSelector`** (`SineQuaNon.lean`): SInE (Hoder–Voronkov)
  adaptation. Trigger relation precomputed per-module into a persistent env
  extension (`sineQuaNonExt`): for each theorem, its "trigger symbols" =
  relevant constants of its type whose frequency ≤ 3.0 × min-frequency
  (tolerance), with a trigger **deny list** (`Eq`, `And`, `Or`, `ite`,
  `OfNat`, …). Selection = best-first over priority
  `depthFactor^depth × Π tolerances` (`depthFactor = 1.5`),
  frequency-penalized `1 + 0.01·log₂(f+1)`. Bounded by `maxSuggestions`, not
  by depth. Again theorems only.
- **`currentFile` selector**: returns all theorems from `env.constants.map₂`
  (the current module's staged constants), score 1.0, allowing private names
  — the *deterministic* "fresh premises" channel that LeanHammer interleaves
  with SInE in its fallback.
- **Deny lists:** module deny list (Lake/Lean/Internal/Tactic), name deny
  list, type-prefix deny list, `sorryAx`, internal names, deprecated,
  instances.
- Combinators: `<|>` (orElse on failure), `intersperse (ratio := 0.5)`
  (rank-interleave two selectors, both asked for full budget), `interleave`
  in the premise-selection repo (cloud + MePo dedup by rank).

## 6. Cloud client (hanwenzhu/premise-selection, `PremiseSelection/Cloud.lean`; server hanwenzhu/lean-premise-server)

`premiseSelection.apiBaseUrl` (default `http://leanpremise.net`). Client
diffs environment against server's indexed premises
(`getIndexedPremisesFromServer`, per-module indices), collects
`getUnindexedImportedPremises` + `getUnindexedLocalPremises`
(pretty-printed signatures, cap 8192 new premises/request,
`getMaxUnindexedPremises`), then `POST /retrieve` with {goal-state string,
indexed indices, new premise texts, k}. Server embeds new signatures on the
fly; Mathlib/Batteries/core embeddings cached. This is the entire "newly
defined constant" story on the neural side: **signature-text embedding, no
dependency-history features**.

## 7. ReProver / LeanDojo (arXiv:2306.15626) — brief

Dense retrieval (ByT5 encoder) over the corpus of **accessible premises**
determined by program analysis at the proof site; `novel_premises` benchmark
split explicitly tests generalization to premises never used in training
(ReProver 26.3% vs 23.2% no-retrieval). New constants are handled the same
way as LeanPremise: the premise is embedded from its text, so unseen
definitions are retrievable without retraining; no dependency-history
mechanism. Lean's built-in `exact?`/`apply?`/`rw?` are discrimination-tree
indexed over the whole environment, so fresh constants participate
automatically but with no ranking beyond unification.

## Synthesis relevant to the CoqHammer design question

**Nobody in the Lean stack force-includes definitions of goal constants.**
The bounded mechanisms actually used:

1. Selector trained so that definitions used via `rw`/`simp` are *learnable*
   premises (definitions are first-class citizens of the premise corpus).
2. **Lazy, per-premise expansion**: a definition that makes it into the
   premise list is expanded to its Lean-generated equation lemmas
   (`getEqnsFor?`) at fact-elaboration time (Duper `elabFact`, lean-auto
   `d[...]`), recursors to per-constructor ι-equations.
3. Explicit user syntax (`u[...]`/`d[...]`) with a topological-sort
   acyclicity check as the only closure bound.
4. Freshness handled by *selector-level* channels (`currentFile` interleave,
   on-the-fly signature embedding), not by definitional closure.
5. Symbol-based selectors (MePo/SInE) restricted to theorems with
   frequency-based trigger tolerance and deny lists as the boundedness
   devices.
