# Premise-selection literature survey: definitional inclusion and the fresh-constant problem

*Research report, 2026-07-18, for `notes/premises.md` (bounded inclusion of
definitions of constants occurring in the goal and hypotheses). Covers the
hammer/premise-selection literature beyond Sledgehammer and LeanHammer (see
the companion reports `premise-selection-sledgehammer.md` and
`premise-selection-leanhammer.md`; codebase ground truth in
`premise-selection-coqhammer-dataflow.md`). Archived papers cited below live
in `notes/papers/`.*

## 1. CoqHammer's own papers

**Czajka & Kaliszyk, "Hammer for Coq: Automation for Dependent Type
Theory", JAR 61(1–4):423–453, 2018**
(`notes/papers/czajka-kaliszyk-hammer-for-coq-jar2018.txt`). Premise
selection is Section 4, performed at the CIC₀ level, reusing "the two most
successful filters used in HOLyHammer and Sledgehammer."

- **Features** F(T): the constants (term and type constants) appearing in
  the statement, omitting basic logical constants; variables all replaced by
  one symbol X; plus parse-tree edge features: constant–constant and
  constant–variable pairs sharing an edge in the parse tree (written e.g.
  `"Coq.Init.Peano.le-X"` for a constant applied to a variable;
  constant-constant applications like successor-of-zero give compound
  features). Example given for `Between.between_le`.
- **Feature weights**: w(f) computed by TF-IDF (citing Sparck Jones 1972),
  "This ensures that rare features are more important than common ones."
- **Dependencies** D(T): "the constants occurring in the type of T or in the
  proof term (or the unfolding) of T." Explicitly noted as possibly
  incomplete: an ATP proof may need facts used implicitly in type-checking
  but not present in the proof term, "e.g. definitions of constants, facts
  which are necessary to establish types of certain terms." (Conclusions
  repeat: "the dependencies extracted from the Coq proof terms do miss
  information used implicitly by the kernel, and are therefore not as
  precise as those offered in HOL-based systems.")
- **k-NN**: similarity s(a,b) = Σ_{f∈F(a)∩F(b)} w(f)^τ₁. Relevance of
  visible fact a for goal g given neighbor set N with nearness values:
  (τ₂ · Σ_{b∈N | a∈D(b)} s(b,g)/|D(b)|) + (s(a,g) if a∈N else 0), with
  τ₁=6, τ₂=2.7 "found experimentally in our previous work [Kaliszyk &
  Urban, PxTP 2013]".
- **The "fresh fact / no proof history" fix (verbatim rationale)**: "First,
  when deciding on the labels to predict based on the neighbors, we not only
  include the labels associated with the neighbors ... but also the
  neighbors themselves. This is because a theorem is in principle provable
  from itself in zero steps, and this information is not included in the
  training data. Furthermore, theorems that have been proved, but have not
  been used yet, would not be accessible to the algorithm without this
  modification." Second modification: no fixed k; instead fix the number of
  facts with non-zero relevance, start with k=1 and increase k iteratively —
  "creating ATP problems of proportionate complexity."
- **Sparse naive Bayes**: estimates P(a is used in the proof of g),
  restricted to extended features F̄(a) = F(a) ∪ ⋃_{b : a∈D(b)} F(b). Bayes
  product over F(g)∩F̄(a), F(g)−F̄(a), F̄(a)−F(g), estimated via s(a,f) =
  # times a was a dependency of a fact with feature f, t(a) = # times a has
  been a dependency, K = # theorems proved so far: P(a used in proof of s) =
  t(a)/K, P(s has f | a used) = s(a,f)/t(a). Log-space with smoothing in the
  implementation.
- **Premise counts / Predictions option**: evaluation considered all powers
  of two from 16 to 1024 premises; the greedy strategy schedule (Table 1/3)
  mixes kNN and NB at 16–1024 premises across Vampire/Z3/Eprover (top
  strategy: Vampire, k-NN, 1024 premises). In the current source
  (`src/plugin/opt.ml`) `Set Hammer Predictions` defaults to **1024** (Unset
  → 128; minimum 16).
- **Key quantitative statement on Coq vs HOL** (Conclusions): "for similar
  size parts of the libraries almost the same premise selection algorithms
  used in HOLyHammer or Isabelle/MaSh ... require on average 200–300 best
  premises to cover the dependencies, whereas in the Coq standard library on
  average **499–530 best premises** are required." Overall 40.8% of stdlib
  re-proved push-button.
- **On definitions specifically**: no mechanism to force-include definitions
  of goal constants; whatever is not selected stays uninterpreted in the FOL
  translation. But note: selected premises that are definitions do get their
  defining axioms via the translation (Section 5.1: "Definitions are
  exported as CIC₀ definitions"; induction principles/recursor definitions
  exported as separate definitions). Section 8 case studies repeatedly show
  ATP proofs using *definitions* as premises (e.g. `dist_euc` definition +
  `isometric_rotation_0`; "the definition of ++ (Datatypes.app)") — i.e., in
  practice the learned selectors must rank definitions like any other fact.

**Czajka, "Practical Proof Search for Coq by Type Inhabitation" (sauto,
IJCAR 2020)**: this paper is about the proof search procedure, not premise
selection — it contains no premise selection component. Relevant knobs
(confirmed in this repo, `src/tactics/sauto.mli`): user-supplied lemmas
(`use:`), hint databases (`s_hint_bases`), and *controlled definition
unfolding* — `s_unfolding : Constant.t list soption` (SNone | SAll | SSome),
`s_always_unfold`, `s_aggressive_unfolding`, `add_unfold_hint`. So on the
reconstruction side CoqHammer already has a per-constant unfolding
mechanism; the selection side has none.

## 2. HOLyHammer / Flyspeck (Kaliszyk & Urban)

**"Learning-Assisted Automated Reasoning with Flyspeck" (JAR 53(2), 2014;
arXiv:1211.7012,
`notes/papers/kaliszyk-urban-2014-flyspeck-learning-assisted-jar.txt`)**:
- Features: symbols + normalized terms/subterms; variants syms0 (all
  variables → A0), syms (variables numbered A0, A1, ...), sym**st**
  (variables renamed to their type, e.g. `Anum`, `Areal` — type-aware
  variable abstraction), symsd. Also all normalized atomic formulas and
  component terms recursively.
- Dependencies: ITP (HOL Light) dependencies exported; ATP proofs
  *pseudo-minimized* (re-run with only used premises, iterated) and
  *cross-minimized* (each proof re-run by all ATPs); preference "minweight:
  always prefer the minimal ATP proof if available." Learning on
  ATP-minimized dependencies beats learning on raw ITP dependencies.
- Dealing with pathological dependencies: "obviously unhelpful dependencies
  were filtered manually," e.g. AND_DEF (definition of ∧) is a dependency of
  14122 theorems. (Facts never used in proofs are handled by the kNN
  self-inclusion trick, same engine as above, plus feature similarity.)
- Premise thresholds: 8, 32, 128, 512, ...; 39% of 14185 Flyspeck theorems
  provable push-button in 30 s on 14 CPUs.

**"Stronger Automation for Flyspeck by Feature Weighting and Strategy
Evolution" (PxTP 2013, EPiC 14, pp. 87–95)** — origin of the IDF weighting
used by CoqHammer:
- IDF(t,D) = log(|D| / |{d∈D : t∈d}|); also two variants found useful:
  IDF₁(t,D) = 1/(1+|{d∈D : t∈d}|) (smoothed inverse frequency) and
  IDF₂(t,D) = 1/(1+|{d∈D : t∈d}|)² (quadratically scaled).
- Distance-weighted multiclass k-NN (Dudani 1976): weighs contribution of
  the k nearest neighbors by feature-based similarity to the conjecture;
  ranking = sum of premises' weighted contributions from the k neighbors.
  "The frequency-scaling code ... takes about 5 lines of Perl; the whole
  sparse distance-weighted multiclass k-NN ... about 200 lines."
- Results: log-scaled IDF best; with log IDF only few neighbors needed
  (best single method 40-NN_IDF with 128 premises, E prover: 31.43%).
  Overall 14-method coverage 39.0% → 45.45% (16% relative). Best single
  premise-selection/ATP combination +30% (24.2% → 31.4%).
- Notable acknowledgment: "the idea of using the inverse document frequency
  ... is in some sense also at the heart of the SInE axiom-selection
  heuristic developed independently by Kryštof Hoder." Footnote 3:
  "SInE-based selection is obviously interacting in various ways with the
  premise selection done by naive Bayes and k-NN. This typically turns out
  to be a fruitful interaction of two different ranking methods." In the
  BliStr-evolved E strategies, SInE appears **inside** 11/14 resp. 12/14
  best strategies, often with recursion (depth) limited to 1 or 2 — i.e.,
  an evolved two-phase pipeline: learned selection of N premises, then
  trigger-based SInE pruning inside the ATP.

**MizAR 40 for Mizar 40 (JAR 55(3), 2015; arXiv:1310.2805,
`notes/papers/kaliszyk-urban-2013-mizar40-for-mizar40.txt`)**: kNN family
with IDF gave "quite significant performance improvement"; also naive Bayes
with IDF (nbidf); features as in MaLARea (symbols, terms, subterms;
variables → A0); 40.6% of Mizar toplevel theorems proved by the union of
methods.

## 3. MaSh/MePo/MeSh (brief; formulas match CoqHammer's ancestors)

**Blanchette, Greenaway, Kaliszyk, Kühlwein, Urban, "A Learning-Based Fact
Selector for Isabelle/HOL", JAR 57(3):219–244, 2016**
(`notes/papers/blanchette-greenaway-kaliszyk-kuhlwein-urban-2016-fact-selector-jar.txt`):
- **MePo**: iterative; keeps a set of "known" symbols (initially the
  goal's); fact score ≈ k/(k+u) (k = known, u = unknown symbols in the
  fact); select perfect-score facts + some high scorers, add their symbols
  to known, repeat until n facts. Refinements: chained facts get absolute
  priority; local > global facts; first-order > higher-order; rare symbols
  weighted more. Failure modes named: discriminates poorly when all symbols
  are common; "starvation" (best-first expansion may ignore useful facts
  close to the root). Example 2: MePo ranks a needed lemma 3742nd because of
  many non-goal symbols; MaSh ranks all four needed lemmas within the top
  35.
- **MaSh NB/kNN**: identical structure to CoqHammer's (CoqHammer adapted
  these): NB log-relevance = σ₁ ln t(φ) + Σ_{f∈F(γ)∩F̄(φ)} w(f)
  ln(σ₂ s(φ,f)/t(φ)) + σ₃ Σ_{f∈F̄(φ)−F(γ)} w(f) ln(1 − (s(φ,f)−1)/t(φ)) +
  σ₄ Σ_{f∈F(γ)−F̄(φ)} w(f), with σ₁=30, σ₂=5, σ₃=0.2, σ₄=−18. kNN nearness
  n(φ,χ)=Σ_{f∈F(φ)∩F(χ)} w(f)^τ₁, relevance
  (τ₂ Σ_{χ∈N | φ∈Π(χ)} n(χ,γ)/|Π(χ)|) + (n(φ,γ) if φ∈N), τ₁=6, τ₂=2.7.
  Explicit rationale: "The dependencies of a fact φ are useful for proving
  φ, and **φ is useful for proving itself**" — the right summand is exactly
  the fresh-fact fix. k grows from 0 until enough facts have nonzero
  relevance.
- **IDF**: w(f,Φ) = ln(|Φ| / |{φ∈Φ | f∈F̄(φ)}|).
- Features: nontrivial first-order patterns to depth 2 with variables
  replaced by their **types** (e.g. `h(τ,a)`, `g(h)`); types themselves and
  type classes as features; theory name and locality as metafeatures.
  Chained facts' features added at half weight; features of up to 10
  preceding facts at weight 0.1 (proximity prior for goals with few
  features).
- Learning data hygiene: logic-tautology dependencies dropped; proofs with
  >20 dependencies considered unsuitable and ignored; prefer
  machine-minimized (Sledgehammer/Metis) proofs over Isar proofs for
  learning.
- **Fresh facts, operationally**: on each invocation, if <100 facts are
  unknown to the learner they are learned **synchronously before the
  query**; otherwise a background thread learns them. "But even then, these
  new facts will typically appear in few proofs, regardless of how useful
  they may be" → as a precaution the raw MaSh ranking is blended with a
  **proximity selector** (facts sorted by closeness in the proof text):
  ranks are mapped through empirical rank→probability curves and averaged
  with weights 0.8 (MaSh) / 0.2 (proximity).
- **MeSh** (hybridization): combine MePo and MaSh rankings the same way,
  each weighted 0.5, using the MaSh probability curve; "inspired by
  experiments combining machine learning with the MePo-like SInE selector"
  (Kühlwein et al.). The steep curves "ensure that if a fact is ranked very
  high by either MaSh or the proximity selector, it will be ranked very
  high in the result" — i.e., score-mixing engineered to behave like
  union-of-top-slots. Motivation for keeping MePo at all: robustness on
  unseen material and on new facts with no proof history; evaluations show
  MeSh sometimes helped, sometimes hampered by its MePo component, but it
  is the default because it hedges the cold-start case. n=1024 facts in ML
  evaluations; provers get prefixes m ≤ n (50–1000 depending on time
  slice).

## 4. Neural premise selection — handling unseen definitions

**DeepMath (Alemi, Chollet, Irving, Szegedy, Urban, NIPS 2016;
arXiv:1606.04442, `notes/papers/alemi-etal-2016-deepmath-neurips.txt`)**:
char-level CNN/RNN embeddings of formulas (80-dim one-hot chars, ≤2048
chars); word-level stage on top. Rare-symbol problem: 60.3% of Mizar
symbols occur <10 times. Solution: **definition-aware embeddings
("def-CNN")** — each defined symbol's word embedding is the
*character-level CNN embedding of the statement defining it* (one level, no
recursive expansion; brackets/operators get fixed pseudo-random vectors).
This makes the model closed under new definitions: a new symbol's embedding
is computed from its definition text at inference. def-CNN best single
model: 1822/2742 theorems (66.4%) proved at k=1024 vs distance-weighted kNN
baseline 1786 (65.1%); union of all methods 78.4%. Hard negative mining was
critical (61.3% → 66.4%).

**Magnushammer (Mikuła et al., ICLR 2024; arXiv:2303.04488,
`notes/papers/mikula-etal-2023-magnushammer-arxiv.txt`)**: two stages.
SELECT: batch-contrastive (modified InfoNCE) training of a shared
transformer producing proof-state and premise embeddings; cosine
similarity; retrieves K_S=1024 from 30–50K available (433K premise database
total); premise embeddings **cached**, one network pass per query. RERANK:
scores each (proof_state, premise) pair jointly with cross-entropy-trained
head, re-ranks the K_S (K_R=K_S). RERANK negatives: 15 hardest false
positives sampled from SELECT's top-1024 never-used premises per state.
SELECT batches: N states, N positives, M=3N extra negatives. Data: 4.4M
(proof_state, premise) pairs (HPL 1.1M human + SH 3.3M
Sledgehammer-generated). Text-based: premises are embedded from their
statements, so unseen premises are handled by embedding at inference (no
symbol vocabulary); data-efficient (outperforms Sledgehammer with 4K
training examples). Results: PISA 59.5% vs Sledgehammer 38.3%, BM25 30.6%,
TF-IDF 31.8%, OpenAI ada-002 embeddings 36.1%; miniF2F 34.0% vs 20.9%.
Evaluation protocol: for each of a set of tactics, try top-k premises for
k ∈ powers of 2 up to 2¹⁰ (echoes the classic multi-slice premise-count
schedule). Limitation they name themselves: proof-state text "does not
provide complete semantic information about the referenced objects.
**Including function definitions and object types in the proof state
representation might further improve performance**."

**ReProver / LeanDojo (Yang et al., NeurIPS 2023; arXiv:2306.15626,
`notes/papers/yang-etal-2023-leandojo-reprover-neurips.txt`)**: dense
retrieval with a ByT5 (byte-level, so no OOV tokens) encoder, average
pooling, cosine similarity. **Accessible premises**: program analysis
restricts the candidate set to premises defined earlier in the file or
transitively imported (avg 33K of 128K) — a deterministic visibility filter
before learned ranking. Training: contrastive loss with **in-file
negatives** (k negatives from the same file as the positive + n−k random) —
targeting the failure mode of retrieving merely co-located premises.
Retrieves 100 premises; concatenation with the state truncated to model
context for the tactic generator. BM25 baseline much worse (R@1 6.7% vs
13.5%). New premises are handled by encoding statements at inference
(corpus embeddings recomputed per repo via LeanDojo extraction).

**Graph2Tac + Tactician's online kNN (Blaauwbroek, Olšák, Rute, Schapposnik
Massolo, Piepenbrock, Pestun, ICML 2024; arXiv:2401.02949,
`notes/papers/rute-etal-2024-graph2tac-arxiv.txt`)** — the most directly
relevant to the fresh-definition problem:
- Thesis: *locality* — "the physical proximity between two formal
  mathematical concepts is a strong predictor of their mutual relevance" —
  exploited via online learning; online solvers "far surpass offline
  learners when asked to prove theorems in an unseen mathematical setting."
- **Tactician online kNN** (Blaauwbroek, Urban, Geuvers, arXiv:2003.09140;
  CICM 2020 system arXiv:2008.00120,
  `notes/papers/blaauwbroek-urban-geuvers-2020-tactician-cicm.txt`):
  features of the proof state = identifiers plus one-shingles and
  two-shingles (adjacent identifier pairs) of the AST; kNN over a database
  of state–tactic pairs; Jaccard similarity optionally TF-IDF-weighted:
  sim = Σ_{x∈A∩B} tfidf(x) / Σ_{x∈A∪B} tfidf(x) (per the companion study
  Zhang, Blaauwbroek et al., "Online Machine Learning Techniques for Coq: A
  Comparison", CICM 2021; arXiv:2104.05207, which also adds top-down AST
  walks up to length 3, vertically abstracted walks, separate premise/goal
  feature spaces, occurrence counts; online random forest with
  Gini-impurity leaf splitting slightly beats kNN, 36.2% vs 34.7%, union
  40.4% of stdlib in 40 s). Model is updated immediately after every proof —
  no train/test gap; new lemmas usable the moment they are proved.
  Graph2Tac's online kNN variant searches the **1000 most recent tactic
  proof steps** in the global context; offline kNN uses LSH forests. Online
  vs offline kNN: 25.8% vs 15.0% (1.72x) on unseen packages.
- **Graph2Tac definition task**: all Coq kernel objects in one shared
  mono-graph (definitions referenced by edges, α-equivalence-hashed subterm
  sharing); proof states and definitions are subgraphs pruned to 1024
  nodes; 8-hop message-passing GNN (h_dim=128, per-hop graph convolution +
  2-layer MLP + residual/Layernorm). A learned **definition-embedding
  table** holds embeddings for training-time definitions; a **definition
  network** is co-trained (loss = cosine similarity to the table entries,
  combined loss L = 1000·L_def + L_tactic) to *compute* an embedding from a
  definition's graph (root nodes masked). At inference, "for new
  definitions not seen during training, we first calculate an embedding
  using the definition task. If there are multiple new definitions, we
  compute embeddings from each definition graph individually, updating the
  embeddings in a **topologically sorted order** so that those for
  dependencies are computed before those for latter definitions which
  depend on those dependencies." Embeddings are hierarchical — a new
  definition's representation is built from the representations of its
  component definitions. Tactic-argument prediction (global arguments =
  definitions/lemmas) then works by inner product of an argument-query
  embedding against the (dynamically extended) definition table — so **new
  lemmas are predictable as tactic arguments without retraining**.
- Results: definition task 17.4% → 26.1% (1.5x, G2T-Anon-Update vs
  G2T-NoDef-Frozen with random frozen embeddings for new definitions);
  adding name embeddings (LSTM over the qualified identifier string)
  slightly *hurts* (G2T-Named-Update < G2T-Anon-Update — the authors wonder
  if names make the definition task too easy). kNN-online + G2T-Anon-Update
  combined 33.2% (1.27x over each alone; highly complementary since they
  use orthogonal online data: recent *proofs* vs new *definitions*). Both
  beat "CoqHammer combined" (all 4 ATPs + `best` reconstruction) and a
  GPT-2-style transformer baseline by ≥1.48x at 10 min/theorem. Figure 7:
  broken down by number of new dependencies of the test theorem (0, 1–10,
  11–100, 101+), online models dominate as soon as a theorem has ≥10
  dependencies unseen in training.

## 5. SInE (Hoder & Voronkov, "Sine Qua Non for Large Theory Reasoning", CADE 2011, LNAI 6803, pp. 299–314)

The precise algorithm (this is the principled bounded definitional-closure
device):
- Setting: large axiom set Ax + goal G; symbol = predicate/function symbol
  including constants, excluding =.
- Plain symbol-based relevance (Sect. 2.1): symbols are *neighbours* if
  they occur in the same axiom; relevance = reflexive-transitive closure
  from goal symbols; useless in practice because *common symbols* (e.g.
  `instance-of`, `subclass`) make everything relevant, even with k-step
  bounding.
- **Trigger-based selection (Definition 1)**: given a relation
  trigger(s,A) ⊆ {(s,A) | s occurs in A}: (1) every symbol occurring in the
  goal is 0-step triggered; (2) if s is k-step triggered and s triggers A,
  then A is (k+1)-step triggered; (3) if A is k-step triggered and s occurs
  in A, then s is k-step triggered. An axiom/symbol is triggered if
  k-triggered for some k ≥ 0.
- **Sine trigger relation (Definition 2)**: let occ(s) = number of axioms
  in which s appears. trigger(s,A) iff for all symbols s′ occurring in A:
  occ(s) ≤ occ(s′). "An axiom is only triggered by the least common symbols
  occurring in it." Motivation stated: trigger approximates "s₂ is defined
  in terms of s₁" / "more common ≈ more general" — a defining axiom of f is
  *owned* by f (its least common symbol), so the closure from goal symbols
  pulls in precisely the defining axioms of goal symbols, then of the
  symbols those definitions introduce, etc. Worked example
  (subclass/beer/liquid) shows incompleteness: the goal's symbols may fail
  to trigger a needed fact whose least-common symbol is not yet reached;
  also non-monotonic in the axiom set (removing an axiom can cause *more*
  axioms to be selected).
- **Tolerance (Definition 5)**: t ≥ 1: trigger(s,A) iff
  occ(s) ≤ t·occ(s′) for all s′ in A. Selected set is monotone in t; for t
  large enough it degenerates to full symbol-based relevance. Vampire:
  `--sine_tolerance t`, default 1.
- **Depth (Sect. 4.2)**: compute only d-step triggered axioms; Vampire
  `--sine_depth d`, default ∞; selected set monotone in d.
- **Generality threshold (Definition 7)**: g ≥ 1: trigger(s,A) iff
  occ(s) ≤ g **or** for all s′ in A, occ(s) ≤ occ(s′) (with tolerance:
  occ(s) ≤ g or occ(s) ≤ t·occ(s′) ∀s′). Rare symbols (occ ≤ g) trigger
  *every* axiom they occur in. Vampire `--sine_generality_threshold g`,
  default 0.
- Complexity: two-phase. Goal-independent preprocessing: count occ, store
  (s,A) trigger pairs — linear in Ax, shareable across problems; goal phase
  linear in the size of the *selected* set (index on first argument).
  Variant storing (A_i,t_i) pairs sorted by minimal triggering tolerance
  allows arbitrary-tolerance queries after one preprocessing pass
  (n log n).
- Experiments (TPTP: SUMO ~298K axioms, CYC ~3.34M, Mizar ~45K): number of
  iterations to closure can be large (up to 135 CYC, 61 Mizar, 39 SUMO).
  Generality threshold turned out droppable — "all the problems Vampire
  could solve, could also be solved with g = 0"; tolerance and depth are
  both essential. Tolerance is the more stable knob: all solvable CYC
  problems solved with t = 1.2 or higher; 155/231 hard Mizar problems
  solved by every tolerance tried; depth is fragile (39 hard Mizar problems
  solvable with exactly one depth value among 1,2,3,4,5,7,10,∞). Mizar
  problems select much larger sets even at d=1 (>4000 axioms) because Mizar
  goals have many symbols — a caveat for ITP-style goals. Among TPTP
  problems with ≥80000 atoms, 373 solved total, 138 *only with* SInE, 3
  only without. CASC LTB: SInE won 2008; used by the top four systems in
  2009 and by 5/7 incl. winner in 2010. Vampire also exposes
  `--mode axiom_selection` (selection only, TPTP out).
- Related work section situates: Meng–Paulson MePo =
  percentage-of-known-symbols variant with common-symbol penalization;
  Plaisted–Yahya relevance restriction; semantic selection (Pudlák; SRASS);
  latent semantic analysis; MaLARea (ML on previous proofs).

## 6. SRASS (Sutcliffe & Puzis, CADE-21 2007, LNCS 4603, pp. 295–310)

PDF not obtainable (paywalled; abstract-level sources only) — details below
are medium-confidence: axioms are first ordered by a *syntactic relevance*
measure (symbol-overlap-based distance to the conjecture); the semantic
loop then maintains a selected set S, uses a finite model finder to build a
model of S ∪ {¬conjecture}; while such a model exists, it scans the
syntactically-ordered unselected axioms for the first one *false* in the
current model and adds it (an axiom false in the model actually constrains
the search away from the countermodel — axioms true in the model add
nothing semantically); terminates when no model is found (unsatisfiability
likely) or resources run out, then hands S to an ATP. Confirmed from search
snippets: "selection is determined by semantics of the axioms and
conjecture, ordered heuristically by a syntactic relevance measure"; solved
problems the underlying ATP could not solve alone. The same idea family:
Pudlák's semantic premise selection (2007) and MaLARea SG1 (Urban,
Sutcliffe, Pudlák, Vyskočil, IJCAR 2008) which mixes learned selection with
model-based semantic features.

## 7. Two-phase / hybrid selection patterns found

- **MeSh** (§3): learned + symbolic combined by rank→probability curves,
  weights 0.5/0.5; MaSh alone is additionally blended with a proximity
  (recency-in-text) prior 0.8/0.2 explicitly *because new facts have no
  proof history*. Score-mixing with steep curves rather than reserved
  slots, deliberately tuned so a top rank from either selector survives;
  authors note the curves/weights "would ideally be learned."
- **Sledgehammer chained facts**: absolute priority (true reserved slots)
  for facts the user chained into the goal — the one place a hammer
  force-includes facts regardless of ranking.
- **ML-then-SInE** (PxTP 2013, §2): learned selector produces an N-premise
  problem; BliStr-evolved E strategies then apply SInE *inside* the ATP
  with depth limited to 1–2 on that slice; present in 11–12 of the 14 best
  evolved strategies. This is an empirical two-phase pipeline: learned
  ranking bounds the space, trigger-based closure re-prunes per-strategy.
- **Deterministic visibility filter + learned ranking**: ReProver's
  accessible-premises program analysis (§4) — a deterministic pre-phase
  (definitional/import closure) feeding a learned ranker; also LeanDojo
  hard-negative design exploits the same file-locality structure.
- **Complementary online sources**: Graph2Tac (new-definition embeddings) +
  online kNN (recent proofs), combined by running both solvers on split
  time budgets (aggregate solver, 1.27x) — union-of-portfolios rather than
  score fusion.
- **ATPboost** (Piotrowski & Urban, IJCAR 2018): premise selection as
  binary ML in a feedback loop with ATP-confirmed proofs (multiple proofs
  per theorem used as growing training data) — relevant precedent for
  bootstrapping labels when proof history is thin.
- Multi-slice premise counts everywhere: powers-of-two schedules (8...1024)
  in HOLyHammer, Sledgehammer time slices (50–1000 facts), CoqHammer
  (16–1024), Magnushammer (2⁰...2¹⁰) — the standard hedge against not
  knowing the right cutoff.

## Cross-cutting observations for the design question

1. The established fix for "fact with no proof history" in the kNN family
   is exactly one line: **every fact is a (zero-step) proof of itself**, so
   pure statement-similarity can surface never-used facts (CoqHammer JAR
   §4.2; MaSh JAR §3.4). Naive Bayes gets this only indirectly via extended
   features. Neither *forces* the definitions of goal constants in.
2. CoqHammer's dependency notion D(T) already includes "constants occurring
   in the type of T" — i.e., the label side treats mentioned constants as
   dependencies — but selection is still purely ranked; nothing guarantees
   the defining axioms of goal constants enter the ATP problem, and the
   paper itself flags exactly this gap ("definitions of constants, facts
   which are necessary to establish types of certain terms" are missing
   from learned dependencies).
3. SInE is the only principled *bounded closure* algorithm in this
   literature: from goal symbols, repeatedly add axioms "owned" by
   already-reached symbols (ownership = least-commonness within the axiom,
   slack t, rare-symbol override g, bound d). Parameters that mattered
   empirically: t (stable, ≈1.2–3), d (powerful but fragile), g
   (droppable). Its known failure mode for ITP-style goals: goals with many
   symbols trigger huge sets even at d=1.
4. Neural systems answer the fresh-definition problem in three distinct
   ways: (a) compute the embedding *from the definition body* at inference
   (DeepMath def-CNN, Graph2Tac definition task with topological-order
   updates — the strongest evidence: 1.5x on unseen packages, and effect
   grows with the number of new dependencies); (b) vocabulary-free
   statement encoding + on-the-fly premise embedding (Magnushammer,
   ReProver/ByT5); (c) online instance-based learning over recent proofs
   (Tactician kNN, 1.72x). Magnushammer explicitly lists "including
   function definitions ... in the proof state representation" as future
   work — i.e., even the strongest text retriever does not yet see
   definitions of mentioned constants.
5. Empirical datum specific to Coq: the same selectors need ~500 premises
   to cover dependencies on Coq stdlib vs 200–300 on HOL/Isabelle corpora
   (CoqHammer JAR conclusions) — consistent with Coq proofs depending on
   definitional material that statement-similarity ranks poorly.
