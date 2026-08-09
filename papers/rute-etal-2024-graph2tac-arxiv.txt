                                               Graph2Tac: Online Representation Learning of Formal Math Concepts


                                         Lasse Blaauwbroek * 1 Miroslav Olšák * 2 † Jason Rute * 3 Fidel Ivan Schaposnik Massolo 1 Jelle Piepenbrock 4 5
                                                                                          Vasily Pestun 1 3 ‡


                                                                 Abstract                                     with the help of other lemmas. On a high level, entire
                                                                                                              formalization projects concerning different mathematical
                                              In proof assistants, the physical proximity be-
                                                                                                              topics may also depend on one another. The result is an
arXiv:2401.02949v3 [cs.LG] 23 Jun 2024




                                              tween two formal mathematical concepts is a
                                                                                                              enormous web of formal mathematical knowledge. In its
                                              strong predictor of their mutual relevance. Fur-
                                                                                                              center, one finds the most foundational parts of mathematics
                                              thermore, lemmas with close proximity regularly
                                                                                                              such as logic and arithmetic. Towards the outskirts of the
                                              exhibit similar proof structures. We show that
                                                                                                              web, the mathematics becomes increasingly specialized, as
                                              this locality property can be exploited through on-
                                                                                                              knowledge is built towards specific goals such as proving
                                              line learning techniques to obtain solving agents
                                                                                                              the four-color theorem (Gonthier, 2008). As the web of
                                              that far surpass offline learners when asked to
                                                                                                              formal mathematics matures, its core stabilizes into static
                                              prove theorems in an unseen mathematical set-
                                                                                                              knowledge while the outskirts are ever-changing, as new
                                              ting. We extensively benchmark two such online
                                                                                                              insights emerge, connections are made and new theorems
                                              solvers implemented in the Tactician platform for
                                                                                                              are developed.
                                              the Coq proof assistant: First, Tactician’s online
                                              k-nearest neighbor solver, which can learn from                 A good mathematician, whether human or artificial, should
                                              recent proofs, shows a 1.72× improvement in the-                possess a deep and intuitive understanding of the static,
                                              orems proved over an offline equivalent. Second,                foundational core of mathematics. This is gained through
                                              we introduce a graph neural network, Graph2Tac,                 training and practice (in the case of an AI, on a large, off-
                                              with a novel approach to build hierarchical rep-                line corpus). However, a mathematician must also have the
                                              resentations for new definitions. Graph2Tac’s                   capability to quickly gain a working understanding of the
                                              online definition task realizes a 1.5× improve-                 concepts, lemmas, and proving techniques in a new math-
                                              ment in theorems solved over an offline base-                   ematical domain. This is a learned skill. An experienced
                                              line. The k-NN and Graph2Tac solvers rely on                    mathematician can grok a new math concept from its def-
                                              orthogonal online data, making them highly com-                 inition and perhaps by looking at a few examples. For an
                                              plementary. Their combination improves 1.27×                    AI, this amounts to “online representation learning”: It must
                                              over their individual performances. Both solvers                have a procedure to quickly build new representations for
                                              outperform all other general-purpose provers for                concepts, without having to retrain from scratch.
                                              Coq, including CoqHammer, Proverbot9001, and
                                                                                                              In this work, we explore online representation learning
                                              a transformer baseline by at least 1.48× and are
                                                                                                              for the Coq proof assistant (The Coq Development Team,
                                              available for practical use by end-users.
                                                                                                              2023) through the Tactician platform (Blaauwbroek, 2023;
                                                                                                              Blaauwbroek et al., 2020b). This platform provides a large-
                                                                                                              scale dataset and machine-to-machine interaction protocols
                                         1. Introduction                                                      that give an external proving agent (solver) online access to
                                         Formal libraries of mathematics are structured hierarchically.       the full internal formal knowledge base loaded into Coq. We
                                         Definitions build on top of each other and lemmas are proven         evaluate the capabilities of two online solvers, Tactician’s
                                                                                                              built-in k-nearest neighbor (k-NN) solver (Blaauwbroek
                                           *
                                             Equal contribution 1 IHES 2 University of Cambridge 3 IBM        et al., 2020a; Zhang et al., 2021) and a novel model called
                                         Research 4 Radboud University 5 Czech Technical University in        Graph2Tac against a number of baselines.
                                         Prague †Work performed at IHES ‡Work performed while at
                                         IHES and IBM Research until June 2022. Correspondence to:            Figure 1 summarizes the the paradigm of both online solvers.
                                         Lasse Blaauwbroek <lasse@blaauwbroek.eu>, Jason Rute <ja-            During offline training, the model develops a deep under-
                                         son.rute@ibm.com>.
                                                                                                              standing of the mathematics found in a static Coq dataset. It
                                         Proceedings of the 41 st International Conference on Machine         also learns to represent new information in an online man-
                                         Learning, Vienna, Austria. PMLR 235, 2024. Copyright 2024 by         ner. During evaluation, Graph2Tac incorporates information
                                         the author(s).

                                                                                                          1
                             Graph2Tac: Online Representation Learning of Formal Math Concepts

from new definitions and theorems, and the online k-NN                 sure these calculated embeddings agree with the learned
incorporates information from new proofs. When the user                embeddings, we co-train with a definition embedding task
invokes Tactician’s Suggest command, the model uses                    (upper right of the figure) which keeps them aligned. Each
the current state to suggest a next proof step, called a tactic        calculated embedding is hierarchical, depending not only
in Coq. Each tactic is made up of an instruction followed by           on the graph of this definition, but the representations of
arguments. When the user invokes Tactician’s synth tac-                component definitions.
tic, a solver searches for a full proof of the current theorem,
calling the model at each step of the search.                          Contributions We demonstrate the crucial importance of
                                                                       incorporating online information into models. Comparing
                                                                       an offline and online version of the k-NN solver demon-
                                                                       strates a proving performance improvement from 15.0%
                                                                       to 25.8% (1.72x). Section 3.2 introduces a new definition
                                                                       training task for GNNs that improves performance from
                                                                       17.4% to 26.1% (1.5x). Our Graph2Tac model is based on
                                                                       an encoding of Coq’s mathematical knowledge as a single
                                                                       interconnected mono-graph (Section 2) that enables calcu-
                                                                       lating hierarchical representations of definitions. Due to
                                                                       integration with the Tactician platform, Graph2Tac is the
                                                                       first neural network model conveniently available to Coq
                                                                       end-users. Graph2Tac and k-NN are highly complementary,
                                                                       together proving 33.2% of the test set.
                                                                       We compare the online models to a variety of other general-
                                                                       purpose solvers for Coq, including a transformer baseline,
                                                                       CoqHammer, Proverbot9001, ASTactic, TacTok and Pass-
                                                                       port (Section 3.3). Both online solvers prove at least 1.48x
                                                                       more theorems than any of the comparisons, making them
                                                                       the strongest by some margin. An extensive analysis of our
                                                                       experiments is in Section 4 and several appendices. Our
Figure 1. Our two paradigms of online learning: the online k-NN        code is publicly available, and every step of our work is
learns from recent proofs and the GNN (Graph2Tac) from recent
                                                                       fully reproducible (Appendix A).
definitions.

The two online solvers we discuss in Section 3, k-NN and               Background and Related work This work fits into a
Graph2Tac, operate on entirely different kinds of online               growing body of work on machine learning and theorem
data and as a result have orthogonal capabilities (discussed           proving. For a full account, see Appendix C. While the
in Section 3.4). The k-NN solver can learn on-the-fly from             online capabilities of existing models are fairly limited, one
tactic scripts written by users. As a result, it can make highly       common source of online information is argument selection
relevant suggestions when the proof of the current lemma               (also called premise selection or lemma selection), where
bears similarities to the surrounding proofs.                          the model selects useful lemmas or definitions arguments for
                                                                       either the current theorem, proof state, or tactic. In argument
Graph2Tac, shown in Figure 2, is a novel graph neural
                                                                       selection, the proof state and lemmas are encoded via simi-
network (GNN) that, in addition to standard offline learning
                                                                       lar methods and the lemmas most related to the proof states
capabilities, contains a novel definition embedding neural
                                                                       are selected. Proof states and lemmas can be represented by
network and task. Our goal is to provide representations for
                                                                       hand-crafted features (Gauthier et al., 2017), S-expressions
definitions (including theorems) both seen during training
                                                                       (Bansal et al., 2019; Sanchez-Stern et al., 2020), trees (Yang
and inference. For definitions seen during training, the
                                                                       & Deng, 2019), pretty printed text (Yang et al., 2023), or
model learns a table of definition embeddings (center of
                                                                       graphs (Paliwal et al., 2020). They are then encoded with ap-
the figure). These are used for representing definitions in
                                                                       propriate machine learning models. Transformer-language
proof states, where the graph of each proof state is used by
                                                                       based approaches (Han et al., 2021) even forgo argument se-
the proof step neural network to suggest a tactic for that
                                                                       lection, synthesizing lemma arguments directly from mem-
proof state. They are also used for representing lemmas and
                                                                       ory of the training data. While convenient, this removes the
other possible tactic arguments, and are incorporated into
                                                                       ability to predict online arguments.
argument prediction. For new definitions, not seen during
training, the definition embedding neural network computes             Tactician (Blaauwbroek et al., 2020b) uses a different online
an embedding from the definition graph. In order to make               approach, relying on online classifiers (including the afore-

                                                                   2
                              Graph2Tac: Online Representation Learning of Formal Math Concepts




Figure 2. Our novel definition training task. At the center is a table of learned definition embeddings (orange). During training (above
the line), we train both a proof step network to predict tactics (including arguments) and a definition network to calculate definition
embeddings (blue) similar to those in the table. During inference (below the line), the definition network is used to calculated hierarchical
embeddings (blue) for new definitions that may in turn be used to represent proof states and predict tactic arguments.


mentioned online k-NN) to select tactic commands from                    node, avoiding any ambiguity with name resolution. (3)
available proof data.                                                    Local variables are connected to their binders, e.g. ∀, λ, via
                                                                         edges. This eliminates the need for local variable names.
However, none of these methods incorporate online defi-
                                                                         (4) By using a novel graph hashing algorithm (Blaauwbroek
nition information, in neither the representations of proof
                                                                         et al., 2024), equal terms are shared across parts of the graph
states nor lemmas. While some models may use the def-
                                                                         leading to more compact representations.
inition name either as a token or a string (Sanchez-Stern
et al., 2023), they do not “look inside” the definition. This            This mono-graph can contain hundreds of millions of nodes
is the main novelty of Graph2Tac’s hierarchical definition               and is too large for a graph neural network. See Appendix D
representation.                                                          for an illustration. Instead, our models hierarchically pro-
                                                                         cess subgraphs representing proof states and definitions.
2. Graph-based Interaction with Coq                                      Each proof state and definition has a root node in the large
                                                                         graph. To obtain a smaller graph, we calculate the forward
In this work, we use a new graph-based data format to com-               closure from the root node, stopping when a definition node
municate between solvers and Coq. In this format, all Coq                is encountered. Theorems are special cases of definitions
definitions and proof states are stored in one large intercon-           where the root node references both the theorem statement
nected graph (Blaauwbroek, 2024; 2023). Figure 3 shows                   and its proof term. We omit the proof term from the theo-
a subset of this large graph that represents the proof state             rem’s definition graph to reduce the graph size.1 In Figure 3
and environment at the start of the Suggest command in                   each subgraphs received a different color. Each color corre-
Figure 1. This novel graph encoding provides the follow-                 sponds to either T1 , =, f , +, N, or the current proof state
ing advantages: (1) The graph is designed to faithfully en-              of theorem T2 , which is still under construction. Notice that
code all kernel objects in Coq’s environment in a reversible                1
                                                                             This is justified by the principle of proof irrelevance: To use a
manner (2) References to global definitions, such as + in                theorem one does not need to know its proof.
Figure 3, are explicitly referenced by edges to the definition

                                                                     3
                                 Graph2Tac: Online Representation Learning of Formal Math Concepts

                       T1                                                 running a machine learning model. Tactician sends the en-
                                                                          tire mono-graph of global definitions along with the current
                                           proof state                    proof state. The client returns a list of suggested tactics and
                  ∀          prf                                          scores. This integration makes our solver usable in practice
                                                                          and allows us to perform a massively parallel benchmark of
                  @      @        =        @       @                      our model on any Coq Opam package.


                  @      @                 @       @                      3. Description of Solvers
                                  2∗                                      Here, we describe the solvers that are part of the comparison
                   ↑                           hyp 1 (x)                  in this paper, including the online k-NN in Section 3.1, our
                                   f
                                                                          novel Graph2Tac architecture 3.2 and a number of baseline
                                                                          comparisons in Section 3.3.
                             ∀                 λ
                                                                          3.1. Online k-Nearest Neighbor
                            N          +   @           @
                                                                          The fastest practical solver currently available in the Tac-
                                                                          tician framework is an online k-nearest neighbor (k-NN)
                                                   ↑
                                                                          model (Blaauwbroek et al., 2020a). It builds a database of
                                                                          proof states and associated tactics and extracts hand-crafted
Figure 3. A graph-based representation of the example given in            features from those proof states (Zhang et al., 2021). When
Figure 1. Each color represents a unique definition or proofstate
                                                                          the model is queried, it looks up proof states with the most
subgraph. These colored subgraphs are used as inputs to our neural
networks. Green corresponds to the function f , red to the theorem
                                                                          similar features to the current proof state and returns the
T 1, and blue to the proof state from the example. Each node is           corresponding tactics, ordered by similarity. It does not
either a definition node (T 1, f , N, =, +) or a node representing        require any training. The online k-NN uses a simple search
the part of a term. For example, @ is function application, and ↑         over the 1000 most recent tactic proof steps in the global
is a variable whose outgoing edge points to its binder. Edges are         context. We also compare to an offline version that searches
labeled, but not shown here. Triangles represent portions of the          over all currently loaded proofs that are part of our train-
graph which we didn’t expand for clarity. Some nodes are shared           ing data. The offline k-NN uses locality sensitive hashing
by multiple colored regions such as the subgraph for 2∗. Definition       forests (LSHF) to speed up the search, similar to the k-NN
nodes (but not the rest of the definition) are also shared with all       solver found in Tactician2 . See Appendix L for additional
colored regions they touch. The proof terms for T 1 is excluded           k-NN variations and ablations.
from its colored region. See Blaauwbroek (2024) for full details.

                                                                          3.2. Graph Neural Network and Definition Task
                                                                          Graph2Tac primarily consists of two parts, a definition task
T1 and the proof state share the subterm associated with 2∗
                                                                          and a prediction task, shown in Figure 4. The input to
(not drawn in full detail).
                                                                          each of these is a directed graph with labeled nodes and
Mutually recursive definitions, such as inductive datatypes,              edges representing either a definition for the definition task
have multiple root nodes that reference each other. Such                  or a proof state for the prediction task. We additionally
definition clusters are treated as a single unit. The subgraphs           associate metadata with each graph. Definition graphs have
extracted from the mono-graph are topologically ordered ac-               root nodes (node f in the figure), one for each definition
cording to their dependencies, so that they can be processed              defined in that graph. Inductive data types define multiple
in an appropriate order by the neural network.                            mutually dependent concepts in the same graph, e.g. bool,
                                                                          true, false, and may therefore have multiple roots. A
To train the model, a large dataset of proofs is extracted
                                                                          proof state graph comes with local context nodes, one for
where each proof state has an associated tactic. A tac-
                                                                          each hypothesis. Both types of graphs contain definition
tic such as rewrite plus_comm in H is decomposed
                                                                          nodes, which are leaf nodes that reference definitions in
into a base tactic rewrite _ in _, and arguments
                                                                          the global context. With each definition node, we store an
plus_comm and H. While arguments may be arbitrary Coq
                                                                          index to the definition embedding table described in the next
terms and even other kinds of objects, our prediction model
                                                                          paragraph. For the prediction task, in addition to the proof
only predicts local hypotheses or global definitions. See
                                                                          state graph, the input includes the indices of all definitions
Appendix D for more information on the dataset.
                                                                              2
                                                                                We do not limit the offline k-NN to 1000 examples because
The Tactician synth tactic and Suggest command can                        the obvious “recency” selection criterion does not apply.
communicate via this graph format with a Python client

                                                                      4
                            Graph2Tac: Online Representation Learning of Formal Math Concepts




Figure 4. Detailed Graph2Tac model architecture, composed of a definition task (the top path going from the definition of f to its
embedding) and prediction task (the path going from the proof state 2 ∗ x = f x to the predicted tactic apply T1). The edge and node
embedding tables are excluded from the image.


and tactics currently available in Coq’s global context.             embeddings.
There are four learned embedding tables: edge labels and             The transformed graphs are put into a message-passing GNN
node labels (not shown in Figure 4), base tactics that occur         (Figure 4, step B). The GNN consists of 8 hops where the
in the training dataset, and definitions that occur in the           tth hop transforms a node embedding xtn according to the
training dataset. All embeddings have dimension equal to             following two steps:
the model’s hidden dimension, hdim = 128. The definition                                                                    
and node embeddings are constrained to be unit-normalized.
                                                                                       1           X
During inference, the definition table will be dynamically              x̂t+1 = ReLU                       Denseθt (e, xtm )
                                                                                                                             
                                                                          n
updated with new definitions as discussed later.                                         deg(n)          e
                                                                                                m,e : m−→n
We transform the input graph, be it a proof state or defi-
                                                                       xt+1 = Layernorm xt + Dropout0.1 (MLPψt (x̂t+1
                                                                                                                                
nition graph, using the following approach (Figure 4, step              n                                         n ))
A). Each graph is pruned to 1024 nodes. For effective mes-           The first step is a graph convolution layer where each node
sage passing, we duplicate all edges to go in both directions        embedding is updated according to incoming edges from
and also add self-edges. The edges are assigned edge em-             neighboring nodes. Here, deg(n) is the number of incom-
beddings from the corresponding embeddings table. This                                e
                                                                     ing edges m −   → n with target n and edge embedding e.
table has 2E + 1 entries, accounting for the E original edge
                                                                     The dense layer has output dimension hdim . The next step
labels, the E reverse edge labels, and the self-edge label.
                                                                     consists of a 2-layer MLP (Dense, ReLU, Dense) with an
Non-definition nodes are assigned embeddings from the
                                                                     inner hidden dimension of 2hdim , then Dropout, Residual,
node embeddings table based on their node label. Definition
                                                                     and Layernorm. The weights for each hop are separate, but
nodes are instead assigned embeddings from the definition
                                                                     the definition and prediction tasks both use the same GNN
embeddings table, except for the root nodes in the definition
                                                                     backbone, sharing the same weights.
task. Those are masked with null embeddings, as the goal of
the definition task is to predict the corresponding definition       The output of the GNN is a graph with the same structure
                                                                     as the input, but with updated node embeddings. Both the

                                                                 5
                               Graph2Tac: Online Representation Learning of Formal Math Concepts

definition and prediction tasks use mean pooling (Figure 4,                  the two tasks is L = 1000 Ldef + Ltactic .
step C) to obtain a single vector embedding for the graph.
                                                                             During inference, the tactic embedding table is masked for
For the definition task, the pooled embedding is concate-
                                                                             tactics which both occur in the training data and are avail-
nated with each of the embeddings of the root nodes for
                                                                             able in the Coq’s current state. Similarly, the definition
the definition, then fed into a two-layer MLP, and finally
                                                                             embedding table is masked for all definitions available in
unit normalized (step D). Optionally, along with each root
                                                                             the current global context. However, for new definitions
node embedding, we additionally concatenate a name em-
                                                                             not seen during training, we first calculate an embedding
bedding for the definition, using a bidirectional LSTM (not-
                                                                             using the definition task. If there are multiple new defini-
shown) to embed the fully qualified Coq identifier string, e.g.
                                                                             tions, we compute embeddings from each definition graph
“Coq.Init.Logic.and”. For the prediction task, the pooled
                                                                             individually, updating the embeddings in a topologically
embedding is fed into a two-layer MLP (step E). The out-
                                                                             sorted order so that those for dependencies are computed
put is multiplied by the tactic embedding table using inner
                                                                             before those for latter definitions which depend on those
product and put through a softmax layer to obtain the base
                                                                             dependencies.
tactic probabilities.
                                                                             At inference time, the output of the tactic task is a list of
To predict the arguments for a tactic, we use a simple two-
                                                                             tactic suggestions, where each sequence starts with a base
layer RNN (Figure 4, step F). The initial hidden state of the
                                                                             tactic, e.g. apply _ and then contains the arguments for
RNN is the embedding for the chosen tactic in the tactic
                                                                             that tactic, if they are required. We use beam search de-
embedding table. (During training the ground truth tactic
                                                                             coding with a beam width of 256 to generate 256 tactic
is provided as input. The decoding method used during
                                                                             suggestions for each proof state.
inference is described below.) The number of steps of the
RNN corresponds to the number of arguments required by                       We train three models: G2T-Named uses the name embed-
the given tactic.                                                            ding in step D, whereas G2T-Anon does not. G2T-NoDef is
                                                                             trained without a definition task. Each of these is run with
Each argument is predicted as follows (Figure 4, step G).
                                                                             three configurations on the definition model during infer-
The RNN output is fed into a pair of two-layer MLPs (Dense,
                                                                             ence: The Recalc configuration calculates embeddings for
ReLU, Dense), resulting in a pair of query embeddings, one
                                                                             all definitions, Update only calculates embeddings for new
for global argument prediction and one for local argument
                                                                             definitions—i.e. those not seen during training, and Frozen
prediction. The global argument prediction query is unit
                                                                             uses random unit normalized embeddings in place of the
normalized. For global arguments, we take the inner product
                                                                             definition model. G2T-NoDef is only used as G2T-NoDef-
of the global argument query with each definition in the em-
                                                                             Frozen. G2T-Anon-Update is the primary model.
bedding table resulting in a logit for each definition. Since
the inner product is bounded (as both vectors in the inner
product are unit normalized), we scale the global logits by                  3.3. Baselines for Comparison
a learned temperature parameter. For each local argument,                    We formally compare the Graph2Tac and k-NN models
we use the GNN output embedding for that local node in                       with three baselines outlined below. Note that some obvi-
the graph and take the inner product with the local argu-                    ous baselines, such as SMTCoq (Armand et al., 2011) and
ment query. Concatenating the local and global logits and                    Itauto (Besson, 2021) were excluded because they are not
performing softmax we get a distribution over all possible                   general purpose solvers. Furthermore, the online random
arguments.                                                                   forest described by Zhang et al. (2021) is excluded because
Since many of the calculations used in our model take place                  it does not scale to large formalizations.
on variable-size lists of objects, e.g. local arguments, our                 firstorder auto with * As a baseline, we use
implementations rely heavily on ragged tensors in Tensor-                    Coq’s built-in firstorder reasoning tactic combined
Flow (Abadi et al., 2015) and graph tensors in TF-GNN (Fer-                  with the programmable proof search tactic auto, with all
ludin et al., 2022).                                                         available hint databases.
We train on batches of 512 definitions and 512 proof states.                 CoqHammer (Czajka & Kaliszyk, 2018) translates theories
The loss for the definition task is cosine similarity.3 The loss             expressed in Coq to a first-order language understood by the
for the training task is the cross-entropy for the full tactic               external automated theorem provers Vampire, CVC4, Z3
sequence. For example, for the tactic apply T1 the loss                      and Eprover. Once an external proof is found, the premises
is − log P (apply _) − log P (T1 | apply _) using the                        required for the proof are extracted, and the proof is re-
probabilities coming from the model. The combined loss of                    constructed inside of Coq through the sauto family of
    3                                                                        higher-order solving tactics (Czajka, 2020).
      If a definition
             √        graph contains multiple definitions, the loss is
divided by n where n is the number of entry points.                          Proof State Text-based Transformer We implement a


                                                                         6
                            Graph2Tac: Online Representation Learning of Formal Math Concepts

decoder-only transformer baseline that operates on the tex-            During evaluation, each solver is limited by the operating
tual representations of the proof states, and predicts a textual       system to one CPU with two hyperthreads. All processes,
representation of the tactic. We use the GPT2 implemen-                including Coq and any external processes such as neural
tation available via the Transformers Python library (Wolf             networks and ATP’s, must share this CPU. An exception is
et al., 2020). The embedding size is set to 768 and it has 12          made for the Transformer-GPU solver, which is permitted
layers, as in one of the models described in that paper. Our           to utilize a dedicated GPU.
approach is similar to that of Han et al. (2021); Jiang et al.
                                                                       We explore two artificially aggregated solvers, that simulate
(2022); Yang et al. (2023), except our transformer models
                                                                       running n solvers concurrently while still adhering to the
are trained from scratch only on Coq proof data.
                                                                       one-CPU computational budget. The number of theorems
Informal Comparisons Appendix I contains informal com-                 “solved” by the aggregate solvers in time t is the number
parisons to highly relevant neural solvers such as Prover-             solved by any of the components in time t/n. “G2T-Anon-
bot9001 (Sanchez-Stern et al., 2020), ASTactic (Yang &                 Update + k-NN-online” is intended to simulate a solver
Deng, 2019) and their derivatives. Due to technical differ-            capable of learning both from new definitions in the global
ences, a direct comparison was not achievable. Nonetheless,            context and new tactic proof scripts. “CoqHammer com-
we are confident that Graph2Tac and k-NN significantly out-            bined” is an aggregate of all four ATP backends and the
perform these solvers for two reasons. First, CoqHammer                reconstruction tactic called best. This simulates the intent
is known to outperform these neural solvers. Given that                of CoqHammer’s authors to run many backends in parallel,
Graph2Tac and the k-NN significantly outperform Coq-                   while maintaining a fair comparison with other solvers.
Hammer, we can conclude that they also surpass the other
neural solvers. Second, Appendix I contains informal exper-            Results The left plot of Figure 5 shows the fraction of test
iments that directly compare to the k-NN solver.                       theorems solved over time for various solvers. One can see
                                                                       both the progress over time and an indication of the startup
3.4. Capabilities of Graph2Tac vs k-NN vs Transformer                  cost of each solver. The right plot of Figure 5 replaces time
                                                                       with the number of calls to the underlying model, giving an
The Graph2Tac, online k-NN, and transformer solvers are
                                                                       indication of the usefulness of that model’s predictions in
all based on the Tactician platform. Nevertheless, their input
                                                                       search irrespective of model speed.4 . This and other plots
and output capabilities are quite different. The online k-NN
                                                                       remove the results from the hott package because HoTT
model sees tactics and their arguments as a black box. It
                                                                       replaces Coq’s built-in standard library, upon which Coq-
can only predict the exact tactic expressions available in
                                                                       Hammer depends. The tlc package is also removed because
its database. Its power comes from speed and the ability
                                                                       G2T-Anon-Update was able to exploit an inconsistency as
to amend its database with new proof scripts. Graph2Tac
                                                                       explained in Appendix Q.
uses a fixed set of tactics and cannot learn from new proof
scripts. However, it can choose lemmas and hypotheses as               Among the k-NN solvers, the online k-NN solves many
arguments for these tactics. Due to its definition embedding           more theorems (25.8% vs 15.0%) showcasing the impor-
task, it can predict lemmas not available in the training set.         tance of incorporating of recent online proof data. (Further
Finally, the transformer has no online learning capabilities.          k-NN ablations are found in Appendix L.)
However, unlike the k-NN and Graph2Tac, it can gener-
                                                                       Among the G2T solvers, the online solvers using the defi-
ate tactics with arbitrary terms as arguments (but it must
                                                                       nition task to compute embeddings for new definitions out-
“hallucinate” references to new lemmas).
                                                                       perform the G2T-NoDef-Frozen baseline (26.1% vs 17.4%)
                                                                       which does not compute embeddings for new definitions.
4. Evaluation                                                          Note our baseline G2T-NoDef-Frozen performs similarly
                                                                       to the transformer baselines in terms of model calls (and
Experimental Setup To evaluate the performance of the
                                                                       even better in per-time performance). This suggests that
solvers described above, we randomly choose 2000 theo-
                                                                       our baseline is at least comparable to the common trans-
rems from the Coq packages in our testing set. The solvers
                                                                       former baselines in other papers. The addition of names in
are given a time limit of 10 minutes per theorem to syn-
                                                                       G2T-Named-Update fares slightly worse than the main G2T
thesize a proof. To look at package-specific results, we
                                                                       solver G2T-Anon-Update. (Further G2T ablations are found
sample up to 500 test theorems per package with a time
                                                                       in Appendix N.)
limit of 5 minutes. The search procedure utilized by the
solvers based on the Tactician framework is a modification             CoqHammer combined fairs better than the transformer
of Dijkstra’s algorithm that performs iterative deepening in           solver, even the variant using a GPU for model inference.
order to relieve memory pressure and has an optimization                  4
                                                                            Pass rate is also impacted by the number of tactic suggestions
that avoids backtracking between independent subgoals. For             returned in a model call. Too few tactics may lead to the search
more information, see Appendix G.                                      terminating early. Our faster models also return more suggestions.

                                                                   7
                              Graph2Tac: Online Representation Learning of Formal Math Concepts




Figure 5. Fraction of theorems proved over time and per number of calls to the model. Online solvers are dashed, offline solvers are solid,
and symbolic solvers are dotted.


                                                                        complementary as the combined solver G2T-Anon-Update
                                                                        + k-NN is much better than either approach alone. We also
                                                                        see this in the Venn Diagram in Figure 6.
                                                                        To investigate the effect of the online setting, Figure 7 breaks
                                                                        down per-time pass rate by the number of new dependencies
                                                                        not seen during training, including transitive dependencies.
                                                                        The online models significantly outperform the offline mod-
                                                                        els when a theorem has at least 10 new dependencies. See
                                                                        Appendix P for a more in-depth analysis.




        Figure 6. Venn diagram of the theorems proved.


See Appendix J for a detailed breakdown of the CoqHammer
results.
The k-NN solvers benefit from being fast, hence both k-NN
solvers excel at lower time limits. In Appendix I we suggest
the online k-NN is at least as powerful as existing neural
Coq solvers in the literature. However, for higher time limits,
the G2T-Anon-Update model starts to overtake, suggesting
that if larger amounts of search are required, there is value
in more sophisticated neural models. It is similar relative to
model calls.                                                            Figure 7. Cumulative pass rate by number of new dependencies.
Moreover, the online k-NN and G2T approaches are quite

                                                                    8
                           Graph2Tac: Online Representation Learning of Formal Math Concepts

5. Discussion and Future Work
Our definition task improved a neural theorem prover from
17.4% to 26.1% in the difficult setting of proving theorems
in never-before-seen packages. This, in addition to the
success of the online k-NN approach, shows the importance
of online learning in this setting. We leave as future work
how to unify the G2T and online k-NN approaches shown
in Figure 1. Ideally, such a model should also account for
new tactics, as well as learn from how new definitions and
tactics are used in new theorems. One avenue is exploring
if our model can be fine-tuned in real time.
To improve the definition task, given that G2T-Anon-Update
outperformed G2T-Named-Update, we wonder if adding the
names makes the definition task too easy for the model.
There may also be alternatives to our definition task, using
ideas in self-supervised or contrastive learning, or using
social-network-size graph models to process the entire graph
of interconnected definitions at once.
Theorem proving and programming share a lot of similari-
ties and concerns, so it is useful to explore how this work
relates to code generation. We leave open how our methodol-
ogy could apply to text-based models. Retrieval augmented
transformers are a possible approach (Yang et al., 2023), but
may not scale to the full definition hierarchy.




                                                                9
                           Graph2Tac: Online Representation Learning of Formal Math Concepts

Impact Statement                                                       doi.org/10.1007/978-3-642-25379-9_12.
In a world increasingly dependent on technology, the need            Kshitij Bansal, Sarah M. Loos, Markus N. Rabe, Chris-
for verifiably safe and secure hardware and algorithms is              tian Szegedy, and Stewart Wilcox. Holist: An environ-
becoming increasingly urgent. This is even more so as a                ment for machine learning of higher order logic theorem
larger amount of computer code is written by AI agents.                proving. In Kamalika Chaudhuri and Ruslan Salakhutdi-
While interactive theorem provers, such as Coq, have been              nov (eds.), Proceedings of the 36th International Confer-
repeatedly used to verify critical systems, the process is             ence on Machine Learning, ICML 2019, 9-15 June 2019,
still too labor-intensive for widespread adoption. Machine             Long Beach, California, USA, volume 97 of Proceed-
learning research, such as ours, which improves the state              ings of Machine Learning Research, pp. 454–463. PMLR,
of the art in automated theorem proving for ITPs has the               2019. URL http://proceedings.mlr.press/
potential to revolutionize the development of safe and secure          v97/bansal19a.html.
code.
                                                                     Frédéric Besson. Itauto: An extensible intuitionistic SAT
Acknowledgments                                                        solver. In Liron Cohen and Cezary Kaliszyk (eds.), 12th
                                                                       International Conference on Interactive Theorem Proving,
This work was partially supported by the European Regional             ITP 2021, June 29 to July 1, 2021, Rome, Italy (Virtual
Development Fund under the Czech project AI&Reasoning                  Conference), volume 193 of LIPIcs, pp. 9:1–9:18. Schloss
no. CZ.02.1.01/0.0/0.0/15 003/0000466, Amazon Research                 Dagstuhl - Leibniz-Zentrum für Informatik, 2021. doi: 10.
Awards, EU ICT-48 2020 project TAILOR no. 952215, and                  4230/LIPIcs.ITP.2021.9. URL https://doi.org/
by the Czech MEYS under the ERC CZ project POSTMAN                     10.4230/LIPIcs.ITP.2021.9.
no. LL1902. Lasse Blaauwbroek acknowledges travel sup-
port from the European Union’s Horizon 2020 research and             Lasse Blaauwbroek. Tactician’s web of large-scale for-
innovation programme under grant agreement No 951847.                  mal knowledge, December 2023. URL https://doi.
We would also like to thank Alex Sanchez-Stern and Emily               org/10.5281/zenodo.10028721.
First for providing the data used in Appendix I.
                                                                     Lasse Blaauwbroek. The Tactician’s web of large-scale
                                                                       formal knowledge. arXiv preprint, January 2024. doi: 10.
References                                                             48550/arXiv.2401.02950. URL https://doi.org/
Martı́n Abadi, Ashish Agarwal, Paul Barham, Eugene                     10.48550/arXiv.2401.02950.
 Brevdo, Zhifeng Chen, Craig Citro, Greg S. Corrado,
                                                                     Lasse Blaauwbroek, Josef Urban, and Herman Geuvers.
 Andy Davis, Jeffrey Dean, Matthieu Devin, Sanjay Ghe-
                                                                       Tactic learning and proving for the coq proof assistant. In
 mawat, Ian Goodfellow, Andrew Harp, Geoffrey Irving,
                                                                       Elvira Albert and Laura Kovács (eds.), LPAR 2020: 23rd
 Michael Isard, Yangqing Jia, Rafal Jozefowicz, Lukasz
                                                                       International Conference on Logic for Programming, Ar-
 Kaiser, Manjunath Kudlur, Josh Levenberg, Dandelion
                                                                       tificial Intelligence and Reasoning, Alicante, Spain, May
 Mané, Rajat Monga, Sherry Moore, Derek Murray, Chris
                                                                       22-27, 2020, volume 73 of EPiC Series in Computing, pp.
 Olah, Mike Schuster, Jonathon Shlens, Benoit Steiner,
                                                                       138–150. EasyChair, 2020a. doi: 10.29007/wg1q. URL
 Ilya Sutskever, Kunal Talwar, Paul Tucker, Vincent
                                                                       https://doi.org/10.29007/wg1q.
 Vanhoucke, Vijay Vasudevan, Fernanda Viégas, Oriol
 Vinyals, Pete Warden, Martin Wattenberg, Martin Wicke,
                                                                     Lasse Blaauwbroek, Josef Urban, and Herman Geuvers.
 Yuan Yu, and Xiaoqiang Zheng. TensorFlow: Large-
                                                                       The tactician - A seamless, interactive tactic learner and
 scale machine learning on heterogeneous systems. 2015.
                                                                       prover for coq. In Christoph Benzmüller and Bruce R.
 URL https://www.tensorflow.org/. Software
                                                                       Miller (eds.), Intelligent Computer Mathematics - 13th
 available from tensorflow.org.
                                                                       International Conference, CICM 2020, Bertinoro, Italy,
                                                                       July 26-31, 2020, Proceedings, volume 12236 of Lecture
Michaël Armand, Germain Faure, Benjamin Grégoire,                    Notes in Computer Science, pp. 271–277. Springer, 2020b.
 Chantal Keller, Laurent Théry, and Benjamin Werner. A                doi: 10.1007/978-3-030-53518-6\ 17. URL https://
 modular integration of SAT/SMT solvers to coq through                 doi.org/10.1007/978-3-030-53518-6_17.
 proof witnesses. In Jean-Pierre Jouannaud and Zhong
 Shao (eds.), Certified Programs and Proofs - First Inter-           Lasse Blaauwbroek, Miroslav Olšák, and Herman Geu-
 national Conference, CPP 2011, Kenting, Taiwan, De-                   vers. Hashing modulo context-sensitive α-equivalence.
 cember 7-9, 2011. Proceedings, volume 7086 of Lecture                 arXiv preprint, January 2024. doi: 10.48550/arXiv.
 Notes in Computer Science, pp. 135–150. Springer, 2011.               2401.02948. URL https://doi.org/10.48550/
 doi: 10.1007/978-3-642-25379-9\ 12. URL https://                      arXiv.2401.02948.

                                                                10
                           Graph2Tac: Online Representation Learning of Formal Math Concepts

Jasmin Christian Blanchette, David Greenaway, Cezary                 Emily First, Yuriy Brun, and Arjun Guha. Tactok:
  Kaliszyk, Daniel Kühlwein, and Josef Urban. A                      Semantics-aware proof synthesis. Proc. ACM Program.
  learning-based fact selector for isabelle/hol. J. Au-               Lang., 4(OOPSLA), nov 2020. doi: 10.1145/3428299.
  tom. Reason., 57(3):219–244, 2016a. doi: 10.1007/                   URL https://doi.org/10.1145/3428299.
  s10817-016-9362-8. URL https://doi.org/10.
  1007/s10817-016-9362-8.                                            Thibault Gauthier, Cezary Kaliszyk, and Josef Urban. Tac-
                                                                       tictoe: Learning to reason with hol4 tactics. In Thomas
Jasmin Christian Blanchette, Cezary Kaliszyk, Lawrence C.              Eiter and David Sands (eds.), LPAR-21. 21st Interna-
  Paulson, and Josef Urban. Hammering towards QED. J.                  tional Conference on Logic for Programming, Artifi-
  Formaliz. Reason., 9(1):101–148, 2016b. doi: 10.6092/                cial Intelligence and Reasoning, volume 46 of EPiC Se-
  issn.1972-5787/4593. URL https://doi.org/10.                         ries in Computing, pp. 125–143. EasyChair, 2017. doi:
  6092/issn.1972-5787/4593.                                            10.29007/ntlb. URL https://easychair.org/
                                                                       publications/paper/WsM.
Karel Chvalovský, Jan Jakubuv, Martin Suda, and Josef
  Urban. ENIGMA-NG: efficient neural and gradient-                   Zarathustra Amadeus Goertzel, Jan Jakubuv, Cezary
  boosted inference guidance for E. In Pascal Fontaine (ed.),          Kaliszyk, Miroslav Olsák, Jelle Piepenbrock, and Josef
 Automated Deduction - CADE 27 - 27th International                    Urban. The isabelle ENIGMA. In June Andronick and
  Conference on Automated Deduction, Natal, Brazil, Au-                Leonardo de Moura (eds.), 13th International Confer-
  gust 27-30, 2019, Proceedings, volume 11716 of Lecture               ence on Interactive Theorem Proving, ITP 2022, Au-
  Notes in Computer Science, pp. 197–215. Springer, 2019.              gust 7-10, 2022, Haifa, Israel, volume 237 of LIPIcs,
  doi: 10.1007/978-3-030-29436-6\ 12. URL https://                     pp. 16:1–16:21. Schloss Dagstuhl - Leibniz-Zentrum
  doi.org/10.1007/978-3-030-29436-6_12.                                für Informatik, 2022. doi: 10.4230/LIPIcs.ITP.2022.
                                                                       16. URL https://doi.org/10.4230/LIPIcs.
Lukasz Czajka. Practical proof search for coq by type                  ITP.2022.16.
  inhabitation. In Nicolas Peltier and Viorica Sofronie-
  Stokkermans (eds.), Automated Reasoning - 10th Interna-            Georges Gonthier. The four colour theorem: Engineering of
  tional Joint Conference, IJCAR 2020, Paris, France, July             a formal proof. In Deepak Kapur (ed.), Computer Mathe-
  1-4, 2020, Proceedings, Part II, volume 12167 of Lecture             matics, pp. 333–333, Berlin, Heidelberg, 2008. Springer
  Notes in Computer Science, pp. 28–57. Springer, 2020.                Berlin Heidelberg. ISBN 978-3-540-87827-8.
  doi: 10.1007/978-3-030-51054-1\ 3. URL https://
                                                                     Thomas Gransden, Neil Walkinshaw, and Rajeev Raman.
  doi.org/10.1007/978-3-030-51054-1_3.
                                                                       Sepia: Search for proofs using inferred automata. In
Lukasz Czajka and Cezary Kaliszyk.      Hammer for                     Amy P. Felty and Aart Middeldorp (eds.), Automated De-
  coq: Automation for dependent type theory. J. Au-                    duction - CADE-25, pp. 246–255, Cham, 2015. Springer
  tom. Reason., 61(1-4):423–453, 2018. doi: 10.1007/                   International Publishing. ISBN 978-3-319-21401-6.
  s10817-018-9458-4. URL https://doi.org/10.
                                                                     Jesse Michael Han, Jason Rute, Yuhuai Wu, Edward Ay-
  1007/s10817-018-9458-4.
                                                                       ers, and Stanislas Polu. Proof artifact co-training for
Oleksandr Ferludin, Arno Eigenwillig, Martin Blais, Dustin             theorem proving with language models. In International
  Zelle, Jan Pfeifer, Alvaro Sanchez-Gonzalez, Sibon Li,               Conference on Learning Representations, 2021.
  Sami Abu-El-Haija, Peter Battaglia, Neslihan Bulut,                Y. F. Hu. Efficient and high quality force-directed graph
  Jonathan Halcrow, Filipe Miguel Gonçalves de Almeida,               drawing. The Mathematica Journal, 10:37–71, 2005.
  Silvio Lattanzi, André Linhares, Brandon Mayer, Va-                 URL       http://www.mathematica-journal.
  hab Mirrokni, John Palowitch, Mihir Paradkar, Jennifer               com/issue/v10i1/contents/graph_draw/
  She, Anton Tsitsulin, Kevin Villela, Lisa Wang, David                graph_draw.pdf.
  Wong, and Bryan Perozzi. TF-GNN: graph neural net-
  works in tensorflow. CoRR, abs/2207.03522, 2022. URL               Daniel Huang, Prafulla Dhariwal, Dawn Song, and Ilya
  http://arxiv.org/abs/2207.03522.                                     Sutskever. Gamepad: A learning environment for theo-
                                                                       rem proving. In 7th International Conference on Learn-
Emily First and Yuriy Brun. Diversity-driven automated                 ing Representations, ICLR 2019, New Orleans, LA, USA,
 formal verification. In Proceedings of the 44th Inter-               May 6-9, 2019. OpenReview.net, 2019. URL https:
 national Conference on Software Engineering, ICSE                    //openreview.net/forum?id=r1xwKoR9Y7.
 ’22, pp. 749–761, New York, NY, USA, 2022. Associa-
 tion for Computing Machinery. ISBN 9781450392211.                   Jan Jakubuv and Josef Urban. ENIGMA: efficient learning-
 doi: 10.1145/3510003.3510138. URL https://doi.                        based inference guiding machine. In Herman Geuvers,
 org/10.1145/3510003.3510138.                                          Matthew England, Osman Hasan, Florian Rabe, and Olaf

                                                                11
                          Graph2Tac: Online Representation Learning of Formal Math Concepts

  Teschke (eds.), Intelligent Computer Mathematics - 10th         Guillaume Lample, Timothée Lacroix, Marie-Anne
  International Conference, CICM 2017, Edinburgh, UK,               Lachaux, Aurélien Rodriguez, Amaury Hayat, Thibaut
  July 17-21, 2017, Proceedings, volume 10383 of Lecture            Lavril, Gabriel Ebner, and Xavier Martinet. Hypertree
  Notes in Computer Science, pp. 292–302. Springer, 2017.           proof search for neural theorem proving. In NeurIPS,
  doi: 10.1007/978-3-319-62075-6\ 20. URL https://                  2022.
  doi.org/10.1007/978-3-319-62075-6_20.
                                                                  Maciej Mikuła, Szymon Antoniak, Szymon Tworkowski,
Jan Jakubuv, Karel Chvalovský, Miroslav Olsák, Bartosz           Albert Qiaochu Jiang, Jin Peng Zhou, Christian Szegedy,
  Piotrowski, Martin Suda, and Josef Urban. ENIGMA                 Łukasz Kuciński, Piotr Miłoś, and Yuhuai Wu. Mag-
  anonymous: Symbol-independent inference guiding ma-              nushammer: A transformer-based approach to premise
  chine (system description). In Nicolas Peltier and               selection. arXiv preprint arXiv:2303.04488, 2023.
  Viorica Sofronie-Stokkermans (eds.), Automated Rea-
  soning - 10th International Joint Conference, IJCAR             Aditya Paliwal, Sarah M. Loos, Markus N. Rabe, Kshi-
  2020, Paris, France, July 1-4, 2020, Proceedings, Part            tij Bansal, and Christian Szegedy. Graph representa-
  II, volume 12167 of Lecture Notes in Computer Sci-                tions for higher-order logic and theorem proving. In
  ence, pp. 448–463. Springer, 2020. doi: 10.1007/                 The Thirty-Fourth AAAI Conference on Artificial Intelli-
  978-3-030-51054-1\ 29. URL https://doi.org/                       gence, AAAI 2020, The Thirty-Second Innovative Appli-
  10.1007/978-3-030-51054-1_29.                                     cations of Artificial Intelligence Conference, IAAI 2020,
                                                                   The Tenth AAAI Symposium on Educational Advances
Albert Qiaochu Jiang, Wenda Li, Szymon Tworkowski,                  in Artificial Intelligence, EAAI 2020, New York, NY,
  Konrad Czechowski, Tomasz Odrzygózdz, Piotr Milos,              USA, February 7-12, 2020, pp. 2967–2974. AAAI Press,
  Yuhuai Wu, and Mateja Jamnik. Thor: Wielding ham-                 2020. doi: 10.1609/AAAI.V34I03.5689. URL https:
  mers to integrate language models and automated theo-            //doi.org/10.1609/aaai.v34i03.5689.
  rem provers. In NeurIPS, 2022.
                                                                  Bartosz Piotrowski, Ramon Fernández Mir, and Edward
Cezary Kaliszyk and Josef Urban. Mizar 40 for mizar 40.             Ayers. Machine-learned premise selection for lean. In
  Journal of Automated Reasoning, 55(3):245–256, 2015.              Revantha Ramanayake and Josef Urban (eds.), Automated
                                                                    Reasoning with Analytic Tableaux and Related Methods,
Cezary Kaliszyk, Lionel Mamane, and Josef Urban. Ma-                pp. 175–186, Cham, 2023. Springer Nature Switzerland.
  chine learning of coq proof guidance: First experiments.          ISBN 978-3-031-43513-3.
  In Temur Kutsia and Andrei Voronkov (eds.), 6th Interna-
  tional Symposium on Symbolic Computation in Software            Stanislas Polu and Ilya Sutskever. Generative language
  Science, SCSS 2014, Gammarth, La Marsa, Tunisia, De-              modeling for automated theorem proving. arXiv preprint
  cember 7-8, 2014, volume 30 of EPiC Series in Comput-             arXiv:2009.03393, 2020.
  ing, pp. 27–34. EasyChair, 2014. doi: 10.29007/lmmg.
  URL https://doi.org/10.29007/lmmg.                              Alec Radford, Jeff Wu, Rewon Child, David Luan, Dario
                                                                    Amodei, and Ilya Sutskever. Language models are unsu-
Ekaterina Komendantskaya, Jonathan Heras, and Gud-                  pervised multitask learners. 2019.
  mund Grov. Machine learning in proof general. In
  Proceedings 10th International Workshop On User In-             Jason Rute, Miroslav Olšák, Lasse Blaauwbroek, Fidel Ivan
  terfaces for Theorem Provers (UITP 2012), Electronic              Schaposnik Massolo, Jelle Piepenbrock, and Vasily Pes-
  Proceedings in Theoretical Computer Science, pp. 15–              tun. Artifact for: Graph2Tac: Learning Hierarchical Rep-
  41, Australia, 2013. Open Publishing Association. doi:            resentations of Math Concepts in Theorem Proving, De-
  10.4204/EPTCS.118.2.                                              cember 2023. URL https://doi.org/10.5281/
                                                                    zenodo.10410473.
Daniel Kühlwein, Jasmin Christian Blanchette, Cezary
  Kaliszyk, and Josef Urban. Mash: Machine learn-                 Alex Sanchez-Stern, Yousef Alhessi, Lawrence Saul, and
  ing for sledgehammer. In Sandrine Blazy, Christine                Sorin Lerner. Generating correctness proofs with neu-
  Paulin-Mohring, and David Pichardie (eds.), Interac-              ral networks. In Proceedings of the 4th ACM SIG-
  tive Theorem Proving - 4th International Conference,              PLAN International Workshop on Machine Learning
  ITP 2013, Rennes, France, July 22-26, 2013. Pro-                  and Programming Languages, MAPL 2020, pp. 1–10,
  ceedings, volume 7998 of Lecture Notes in Computer                New York, NY, USA, 2020. Association for Comput-
  Science, pp. 35–50. Springer, 2013. doi: 10.1007/                 ing Machinery. ISBN 9781450379960. doi: 10.1145/
  978-3-642-39634-2\ 6. URL https://doi.org/                        3394450.3397466. URL https://doi.org/10.
  10.1007/978-3-642-39634-2_6.                                      1145/3394450.3397466.

                                                             12
                          Graph2Tac: Online Representation Learning of Formal Math Concepts

Alex Sanchez-Stern, Emily First, Timothy Zhou, Zhanna             A. Reproducibility
  Kaufman, Yuriy Brun, and Talia Ringer. Passport:
  Improving automated formal verification using identi-           This paper carefully describes our methods for building,
  fiers. ACM Trans. Program. Lang. Syst., 45(2), jun              training, and testing our models and solvers. Our solvers
  2023. ISSN 0164-0925. doi: 10.1145/3593374. URL                 are intended for use by both researchers and Coq end-users.
  https://doi.org/10.1145/3593374.                                For end-users, we provide optimized, pre-trained models
                                                                  that can integrate directly with Coq. Installation and usage
                                                                  instructions can be found on Tactician’s website5 . The mod-
The Coq Development Team. The Coq Proof Assistant,                els run on a typical Linux or x86 Mac machine and do not
  July 2023. URL https://doi.org/10.5281/                         require a GPU. The model can also be hosted on an external
  zenodo.8161141.                                                 server (for example, with a GPU), and used by a locally
                                                                  running Tactician instance, via a TCP connection.
Josef Urban. Translating mizar for first order theorem
  provers. In Andrea Asperti, Bruno Buchberger, and               In this paper, we use a freely available dataset of Coq
  James H. Davenport (eds.), Mathematical Knowledge               Data (Blaauwbroek, 2023). Information on the construc-
  Management, Second International Conference, MKM                tion of the dataset can be found in Blaauwbroek (2024) and
  2003, Bertinoro, Italy, February 16-18, 2003, Proceed-          Blaauwbroek et al. (2024). The dataset is freely available
  ings, volume 2594 of Lecture Notes in Computer Sci-             under the original licenses of its constituent Coq projects.
  ence, pp. 203–215. Springer, 2003. doi: 10.1007/                Most of these licenses are open source. However, some
  3-540-36469-2\ 16. URL https://doi.org/10.                      licenses place restrictions on commercial usage. All our
  1007/3-540-36469-2_16.                                          models are trained from scratch, without the use of propri-
                                                                  etary pre-training data.
Thomas Wolf, Lysandre Debut, Victor Sanh, Julien Chau-            To enable the full reproduction of the experiments in this
  mond, Clement Delangue, Anthony Moi, Pierric Cis-               paper, all code, datasets, benchmark parameters, benchmark
  tac, Tim Rault, Rémi Louf, Morgan Funtowicz, Joe               results, and analysis scripts are available in a separate ar-
  Davison, Sam Shleifer, Patrick von Platen, Clara Ma,            tifact (Rute et al., 2023). It includes, among others, the
  Yacine Jernite, Julien Plu, Canwen Xu, Teven Le Scao,           following elements:
  Sylvain Gugger, Mariama Drame, Quentin Lhoest, and
  Alexander M. Rush. Transformers: State-of-the-art                  • Archived versions of all code repositories used in the
  natural language processing. In Proceedings of the                   project. Among others, they include the following:
  2020 Conference on Empirical Methods in Natural Lan-
  guage Processing: System Demonstrations, pp. 38–45,                    – Graph2Tac: Code to train and evaluate the
  Online, October 2020. Association for Computational                      GNN.6 .
  Linguistics. URL https://www.aclweb.org/                               – Text2Tac: Code to train and evaluate the Trans-
  anthology/2020.emnlp-demos.6.                                            former.7
                                                                         – The main Tactician repository.8
Kaiyu Yang and Jia Deng. Learning to prove theorems
  via interacting with proof assistants. In International                – The code repository for Tactician’s API used to
  Conference on Machine Learning (ICML), 2019.                             integrate external agents into Coq.9 This also in-
                                                                           cludes the PyTactician Python library that can be
                                                                           used to extract data from the dataset and interface
Kaiyu Yang, Aidan Swope, Alex Gu, Rahul Chalamala,
                                                                           with Coq.10
  Peiyang Song, Shixing Yu, Saad Godil, Ryan Prenger,
  and Anima Anandkumar. LeanDojo: Theorem prov-                      5
                                                                       Installation instructions: https://coq-tactician.
  ing with retrieval-augmented language models. arXiv             github.io/api/graph2tac
                                                                     6
  preprint arXiv:2306.15626, 2023.                                     Github: https://github.com/IBM/graph2tac
                                                                       PyPI: https://pypi.org/project/graph2tac
                                                                     7
                                                                       Github:                       https://github.com/
Liao Zhang, Lasse Blaauwbroek, Bartosz Piotrowski,                JellePiepenbrock/text2tac
  Prokop Černỳ, Cezary Kaliszyk, and Josef Urban. Online             PyPi: https://pypi.org/project/text2tac
                                                                     8
  machine learning techniques for coq: A comparison. In                https://github.com/coq-tactician/
  Fairouz Kamareddine and Claudio Sacerdoti Coen (eds.),          coq-tactician
                                                                     9
  Intelligent Computer Mathematics, pp. 67–83, Cham,                   https://github.com/coq-tactician/
                                                                  coq-tactician-api
  2021. Springer International Publishing. ISBN 978-3-              10
                                                                       PyPi: https://pypi.org/project/pytactician
  030-81097-9.                                                         Docs: https://coq-tactician.github.io/api/
                                                                  pytactician-pdoc

                                                             13
                            Graph2Tac: Online Representation Learning of Formal Math Concepts

       – The benchmarking system used to evaluate mod-                is inconclusive due to methodological differences. Greater
         els.11 This system allows massively parallel eval-           challenges exist for comparing to solvers in HOL-Light,
         uations of agents on all Coq projects packaged in            Isabelle, and Lean. More standardized benchmarks are
         the Opam package manager.                                    needed.

   • Trained models for Graph2Tac and Text2Tac. They                  The comparisons we did perform also run the risk of not
     correspond exactly with the models used to obtain the            being an apples-to-apples comparison. The G2T and trans-
     results in this paper. We also include the scripts and           former models use different setups. The former uses Tensor-
     parameters used to train these models.                           Flow and custom-written beam search, while the latter uses
                                                                      standard machine learning APIs for PyTorch which may not
   • Benchmark scripts that were used to invoke the bench-            have been as optimized for our setting. Further, our baseline
     marking system for each agent evaluated in this paper.           transformer solver is only an approximation of similar work.
     The scripts include the precise parameters used to in-           The transformer models of Polu & Sutskever (2020); Han
     voke the models, as well as a reference to the precise           et al. (2021); Lample et al. (2022); Jiang et al. (2022); Yang
     Git commit of all involved code.                                 et al. (2023) are larger, pre-trained, and use more resources.
                                                                      It may be that emergent capabilities arise from scaling which
   • The raw data for the benchmarks used in this paper. It
                                                                      are not seen in our smaller models. However, one reason
     includes which theorems were tested on, which were
                                                                      we chose to avoid pretraining (besides parity with our graph
     proved, and how long the solver took in terms of sec-
                                                                      model) is the strong risk that our test data will be leaked
     onds, model calls, and tactic executions. This is all in
                                                                      into the pretraining data. (See the discussion on this topic
     hopes of facilitating future comparison and collabora-
                                                                      in Han et al. (2021).) Also, we were specifically exploring
     tion.
                                                                      models that could be run with the resources available to a
   • Analysis notebooks that distill all the raw data into the        typical Coq user. Similarly, our choice to run CoqHammer
     curated data as presented in this paper. They will allow         on a single thread with default settings may not showcase
     the interested reader to verify our results and perform          its strongest capabilities. See the discussion in Appendix J.
     further analysis.                                                The evaluation in Section 4 and the further ablation in Ap-
                                                                      pendix N of the G2T family of models relies on comparison
The artifact should enable anyone to replicate each stage of          with the G2T-X-Frozen models using random embeddings.
our results, including re-training the models, re-running all         There may be alternative ways to perform this baseline.
benchmarks, and re-doing our analysis. Although reproduc-             Passport (Sanchez-Stern et al., 2023) uses definition em-
ing the entire pipeline would require significant work, we            beddings from names. HOList (Bansal et al., 2019) and
expect that our benchmarking data can be re-used easily for           ProverBot9001 (Sanchez-Stern et al., 2020) use a special
comparison against future solvers.                                    token for unknown definitions.
Users can also train and evaluate their own agents with the           Our choice to split on package was essential to testing our
code we provided and the open dataset. While we trained the           online setting, and comparable to other Coq solvers, but it
graph models for three weeks from scratch on two A100s,               also means our results are more variable. A different split
in Appendix M we show that a model trained in two days                would likely give different pass rates. Even our decision
achieves similar results. Users may also train models on a            to exclude hott and tlc from our results heavily influences
different set of Coq packages, including new or private Coq           our final results. This is different from papers in other ITPs
developments, via the data extraction tools provided with             which split randomly by theorem instead of package. Simi-
the dataset and with our training code.                               larly, we only train one of each model instead of multiple
                                                                      instances, and our models were difficult to reliably train.
B. Threats to Validity                                                This also increases the variability of our results.
                                                                      The data we use decomposes tactics into smaller component
Like other results in machine learning, there are many sub-
                                                                      tactics. This is in contrast to models like PACT (Han et al.,
tleties that we may not have accounted for in this research,
                                                                      2021) which not only do not decompose tactics but also
but here we list the important points to look out for.
                                                                      train on combinations of tactics. It is possible our decompo-
In theorem proving, it is a known challenge to compare to             sition leads to more steps needed for a proof, and this may
other comparable solvers. We are unable to provide a direct           especially punish slower models like the transformer which
comparison in our benchmarking system to most existing                can generate more complicated tactic combinations. Also,
Coq solvers, and the informal comparison in Appendix I                our G2T model uses a fairly simple representation of tactics.
  11                                                                  There are 100s of base tactics (we excluded any that oc-
     Github: https://github.com/coq-tactician/
benchmark-system                                                      curred fewer than 6 times) and one Coq tactic, e.g. apply,

                                                                 14
                           Graph2Tac: Online Representation Learning of Formal Math Concepts

may be represented as many different base tactics in our              we use a graph-based dataset extracted with Coq kernel
model (e.g. one for each possible number of arguments).               knowledge which allows us to develop a graph neural net-
Also, we only allow tactic arguments which are single defi-           work that learns the meaning of definitions by exploiting the
nitions or local context hypotheses. The G2T model has no             hierarchical structure of the data. This architecture tackles
way to predict term arguments, which are common in Coq                the problem of learning online, making use of new defini-
proofs.                                                               tions in new projects.
During benchmarking, it was common to encounter Coq                   In interactive theorem proving settings, the term ‘hammer’ is
errors. In the end, any error we counted as a failed proof            often used to indicate built-in automation (of various kinds,
attempt. Some systematic errors we fixed with patches to              depending on the interactive proving system used). There
Coq, but different solvers led to different errors, and some          has been recent work on learning for which proof states to
were easier to fix than others. Further, an error in a test           invoke other automation in the Thor project (Jiang et al.,
theorem could even cause an error in a later test theorem in          2022).
the same file. CoqHammer had a larger number of errors.
                                                                      Aside from the machine learning guidance on the ITP level,
                                                                      there has also been work on improving the performance of
C. Extended Related Work                                              first-order automated theorem provers (and SMT solvers),
                                                                      that form the foundation for the ‘hammer’ approaches, on
We take some extra space in this appendix to touch upon
                                                                      ITP-derived problems. Work on the ‘hammer’ approach in
more related work.
                                                                      various settings was surveyed in Blanchette et al. (2016b).
In recent years, there have been machine learning ap-                 The ENIGMA system (Jakubuv & Urban, 2017) was orig-
proaches for various interactive theorem proving systems.             inally used on first-order translated versions of problems
In the Coq ecosystem specifically, a series of articles (First        from the Mizar system, there were several improvements on
et al., 2020; First & Brun, 2022; Sanchez-Stern et al., 2023)         the Mizar version (Chvalovský et al., 2019; Jakubuv et al.,
was based on the dataset provided by CoqGym (Yang &                   2020), including a graph-neural-network-based version. A
Deng, 2019), which contains many Coq packages to bench-               similar system was also trained and tested on Isabelle prob-
mark machine learning systems. Other projects in simi-                lems (Goertzel et al., 2022).
lar directions were GamePad (Huang et al., 2019), an in-
teraction system based on the coqtop REPL, and Prover-                D. The Universe of Mathematical Concepts
Bot9001 (Sanchez-Stern et al., 2020). Another line of work
is based on the Tactician system (Blaauwbroek et al., 2020b),         The dataset we utilize is extracted from 120 different Coq
for which implementations of k-nearest neighbors and ran-             packages from the Opam package manager. These packages
dom forest algorithms were built (Zhang et al., 2021). Early          were selected by a SAT solver as the largest mutually con-
systems for Coq were Proof General (Komendantskaya et al.,            sistent set of packages available for Coq v8.11. Their topics
2013) and SEPIA (Gransden et al., 2015) and the experi-               vary wildly, including analysis, compiler and programming
ments by Kaliszyk et al. (2014). A system that is often used          language formalization, separation logic, homotopy type
for comparisons is CoqHammer (Czajka & Kaliszyk, 2018).               theory, and much more. The graph extracted from these
                                                                      formalizations consists of over 250 million nodes, which
For other interactive theorem proving systems, there has
                                                                      encode 520k definitions, of which 266k are theorems, and
also been a lot of work done in recent years. Machine learn-
                                                                      4.6M proof state transformations12 .
ing guidance was used to prove problems from the Mizar
ITP system (Urban, 2003; Kaliszyk & Urban, 2015). Tac-                We divide packages into training and test where no test pack-
ticToe (Gauthier et al., 2017) is an ITP machine learning             age depends on a training package. To do so, we induced a
system for HOL4. For HOLight, there is the HOList (Bansal             random topological order on the Coq packages, with regard
et al., 2019) system. In Isabelle, the Sledgehammer system            to the dependency graph. The resulting list was then split
was also extended with machine learning (Kühlwein et al.,            such that the average percentage of theorems and of proof
2013; Blanchette et al., 2016a). For the recently developed           states in the training split is close to 90% (in our case, it is
Lean system, there are, for example, LeanDojo (Yang et al.,           91.3% of all theorems and 88.8% of all proof states).
2023), integrated decision trees (Piotrowski et al., 2023),
                                                                      Figure 8 shows a rendering of a small section of the dataset.
and work using Language Models (LM) (Han et al., 2021;
                                                                      In particular, only the most basic of mathematical concepts
Lample et al., 2022). There have also been LM-based ap-
                                                                      that are part of the “Prelude” in Coq’s standard library, are
proaches for other systems, for example Magnushammer
                                                                      rendered. The full graph contained in the dataset would be
(Mikuła et al., 2023) for Isabelle and the GPT-f system (Polu
& Sutskever, 2020) for MetaMath.                                         12
                                                                            Roughly half of the definitions are derived from each other
                                                                      through Coq’s module and section mechanism.
Our work is novel compared to the previous related work:

                                                                 15
                            Graph2Tac: Online Representation Learning of Formal Math Concepts




        Figure 8. A rendering of a small section of the known mathematical universe as formalized in the Coq proof assistant.


over 3000 times larger. The graph includes all definitions,           E. Further Details on the G2T Architecture
lemmas, and proof terms in the Prelude, as well as a repre-
sentation of all intermediate proof states that were generated        Here we give further details about the G2T architecture
during the proving process and the partial proof terms gener-         described in Section 3.2.
ated by tactics to transition between proof states. Together,
they form a single, interconnected graph. The graph is fully          Graph Inputs for Definitions and Proof States The in-
de-duplicated, such that every sub-term is represented only           puts to the definition and prediction task are directed graphs.
once (but may be referenced many times).                              In Figure 4, the input to the definition task is a graph corre-
                                                                      sponding to the definition f x := x + x. The graph of f can
The size and color of a node in the rendering is dependent
                                                                      be seen in Figure 3 as the eight node subgraph corresponds
on how many times it is referenced. As nodes get more
                                                                      to all the green edges and all the nodes touching the green
popular, they increase in size. Examples of large nodes are
                                                                      edges. This includes the root node f , the global definition
the universes Prop and Type, the inductive definition for
                                                                      nodes for dependencies N and +, and a number of other
Leibnitz equality and the inductive definitions for true and
                                                                      non-definition nodes for binders (∀ and λ), for function ap-
false. Not all popular nodes are definitions, however. Other
                                                                      plication (@), and for the variable x shown as ↑. The edge
popular mathematical entities include hypotheses that posit
                                                                      labels come with labels that are not shown. Variables do
the existence of natural numbers and booleans, and even
                                                                      not need names since they are connected to their binders via
some anonymous subterms that happen to occur very often.
                                                                      labeled edges. Even though we include the nodes N and +,
The placement of each node is determined by the sfdp force-           we do not include the nodes in their respective definition
directed graph drawing engine of the Graphviz visualization           graphs. This keeps the size of our input graph manageably
suite (Hu, 2005). As a result, related nodes will be rendered         small.
close together. This is particularly apparent for inductive
                                                                      Similarly, in Figure 4, the proof state input to the predic-
definitions and their constructors, where it often appears as
                                                                      tion network corresponds to a proof state with two local
if the constructors are “planets” that orbit around a corre-
                                                                      hypotheses x : N, y : N and the goal ⊢ 2 ∗ x = f x. This
sponding inductive that acts as their “sun”. The color of
                                                                      is almost the subgraph shown with blue edges in Figure 3
each edge is determined by its length as determined by the
                                                                      except it contains an extra local hypothesis y. Like variables,
rendering engine.
                                                                      we do not store the names of local hypotheses in the graph.
                                                                      The triangle 2 ∗ x represents the subgraph of nodes shared
                                                                      between the proof state and T1 . (To compress our graph,
                                                                      common terms are shared.) The nodes in that triangle are

                                                                 16
                            Graph2Tac: Online Representation Learning of Formal Math Concepts

also part of the proof state graph.                                   where · is inner product. The denominator is not needed
                                                                      since both DefTask(gd ) and DefEmb(id ) are unit normal-
In step A of Figure 4, we assign embeddings as follows:
                                                                      ized.

   • Root nodes like f get a null vector of all zeros.                The prediction task loss is calculated as follows. Let
                                                                      Ptactic (T | S) be the probability the model assigns to a
   • Definition nodes like 2, ∗, +, and N are assigned em-            base tactic T given a proof state S. Let Pargi (A | S, T ) be
     beddings from the definition embedding table.                    the probability the model assigns to an argument A (either
                                                                      local or global) given a proof state S and the base tactic T .
   • Other nodes, are assigned embeddings from the node
                                                                      (Notice, even though we use an RNN, the probability of the
     embedding table based only on the node type. These in-
                                                                      ith argument only depends on the tactic and proof state.)
     clude nodes for binders, function application, variables,
                                                                      Then if the ground truth tactic sequence is the base tactic T
     and local constants.
                                                                      with arguments A0 , A1 , ..., An−1 , the loss is calculated as
   • Edges are assigned embeddings according to their edge            the cross entropy
     types (after adding in extra edges as described in Sec-
                                                                         Ltactic := − log Ptactic (T | S) − log Parg0 (A0 | S, T )
     tion 3.2).
                                                                                    − log Parg1 (A1 | S, T ) − ...
While Step A treats local context nodes the same as any                             − log Pargn (An−1 | S, T )
other non-definition node, they become important in Step
G, where we use the GNN embeddings for the local context              Adding New Definitions to the Current State During in-
nodes to select arguments.                                            ference, every time we get to a new theorem, we query Coq
                                                                      (via Tactician) for any new definitions added to the global
RNN for Local and Global Argument Prediction The                      context. This gives us a sequence of definitions d0 , ..., dn−1 .
RNN described in Step F of Figure 4 is a simple two                   For each definition d, we first check if that definition was
layer RNN described mathematically as follows. Let t be               seen during training (using a hash based on the graph repre-
the embedding of the base tactic (apply _ in Figure 4).               sentation). If so, we align the definition index given by Coq
Let p be the pooled embedding of the proof state, that is             to the one we already have. If not, we use DefTask(gd ) to
the mean of all the node embeddings in the output graph               calculate the definition embedding, where gd is the graph
of the GNN. The goal is to compute an embedding xi                    of definition d and DefTask is our definition task neural net-
for each argument position i in the base tactic. (For ex-             work. All the embedding tables are in the neural network,
ample, rewrite _ in _ has two argument positions,                     including the definition embedding table. We may assume,
reflexivity has zero positions, and apply _ has one                   by the order definitions are returned from Coq, that any pre-
position. Hence in the example in Figure 4, there is only             requisite definitions needed to calculated DefTask(gd ) have
one RNN output.) The computation is as follows:                       already been added to the definition embedding table. After
                                                                      calculating DefTask(gd ), we manually update the definition
          (0)
         xi     := p                                                  embedding table to include the newly calculated embedding
           (n)                                                        for d.
         hi := t                               for n ∈ {0, 1}
 (n+1)    (n)                (n)  (n)                                 As an implementation detail, the most expensive part of
xi     , hi+1 := ReLU(Dense(xi , hi ))
                                                                      changing the embedding table is recompiling the network,
The two inputs and two outputs to the dense layer are con-            and this is only needed when we change the size of the table.
catenated. The RNN output corresponding to the ith argu-              To reduce this during inference, we allocate a larger defi-
                  (2)                                                 nition embedding table than needed, similar to a resizable
ment position is xi . This is used as the input to Step G in
                                                                      array.
Figure 4.

The Loss for Definition and Prediction task Given a                   F. Training Details
definition d with index id and graph gd , let DefTask(gd )            Graph2Tac graph models were trained on 8 CPUs (with 128
be the computed embedding for the definition task, and                GB RAM) and 2 NVIDIA A100 GPU cards for about 20
DefEmb(id ) be the embedding in the definition embedding              days. Optimization used the Adam optimizer with a learning
table. The definition loss is the cosine similarity loss              rate of 0.0003 and L2 regularization set to 1.0e-05. Training
                        DefTask(gd ) · DefEmb(id )                    was restarted every 24 hours from the current checkpoint,
        Ldef := 1 −                                                   but we did not save optimizer states between restarts. We
                       |DefTask(gd )| |DefEmb(id )|
                                                                      noticed periodic instability in training and occasionally had
                = 1 − DefTask(gd ) · DefEmb(id )                      to restart training from a checkpoint.

                                                                 17
                               Graph2Tac: Online Representation Learning of Formal Math Concepts

During the design of the model, some hyperparameters, such                    H. All Results
as the coefficient 1000 for the loss, were tuned manually
on a small subset of the training data using other training                   Table 1 shows the results for the 10-minute evaluation where
packages for validation.                                                      packages hott and tlc are excluded.

The transformer was a GPT2-style model (Radford et al.,                       Figure 9 shows the cumulative pass rates for all packages
2019) from the Huggingface Transformers library. The                          and all the models discussed in Section 4. We see that
model was trained to predict the tactics based on the proof                   neither the G2T-Anon-Update nor the online k-NN always
states. To determine whether the model was sufficiently                       performs better. In many cases G2T-Anon-Update either
trained, we monitored the validation accuracy and stopped                     overtakes the online k-NN or appears as if it will overtake
training when the validation performance stagnated.                           the online k-NN if given enough time. As discussed in
                                                                              Appendix Q, the tlc package is special in that G2T-Anon-
The GPU evaluations and the training of the transformer                       Update was able to prove a significant number of theorems
were performed on machines with two 20-core Inter E5-                         using an inconsistent axiom.
2698v4, a working memory of 512 GB RAM, and 8
NVIDIA Tesla V100 GPU cards.                                                        solver                                   pass rate
                                                                                    CoqHammer combined                          0.174
G. Search Procedure Details                                                         G2T-Anon-Update                             0.261
The G2T, transformer, and k-NN models only predict single                           G2T-Anon-Update + kNN-online                0.332
tactics. In order to turn our models into a solver, which                           G2T-Named-Update                            0.241
can find a whole proof, we combine them with the search                             G2T-NoDef-Frozen                            0.175
procedure of Tactician (Blaauwbroek et al., 2020a), namely                          Transformer-CPU                             0.105
Dijkstra’s algorithm13 to explore the tree of possible proofs,                      Transformer-GPU                             0.148
but modified to use iterative deepening instead of a queue.                         firstorder                                  0.075
For G2T and transformer, each possible tactic is scored by                          kNN-offline                                 0.150
the log probability predicted by the corresponding model.                           kNN-online                                  0.258
The length of a path (partial proof) is the sum of the negative
log probabilities of its steps. With iterative deepening, each                         Table 1. Pass rates for 10-minute time limit.
iteration i only explores paths whose distance is below an
                i
upper bound Dmax    (depth first where the tactics are ordered
by score). If an iteration exhausts all valid paths without
finding a proof, the search starts from the beginning with
the new upper bound

                  i+1    i+1        i
                 Dmax = Dmax + 1 + Dextra

         i
where Dextra    is the negative log probability needed to in-
crease the left-most path by one tactic. Our iterative deep-
ening search uses constant memory at the expense of only a
constant multiplicative increase in time.
A Coq tactic can produce multiple independent subgoals.
Each step in our search procedure predicts a tactic for the
first goal of the stack and applies the resulting tactic to that
goal only. If these goals are fully independent (have no
shared E-variables), then our DFS takes this into account
by not backtracking into a previously solved subgoal earlier
in the proof. See Tactician (Blaauwbroek et al., 2020a) for
more details.
  13
     Dijkstra’s algorithm is a special case of best-first search algo-
rithms, and the ”best-first search” of Polu & Sutskever (2020) and
following works (Han et al., 2021; Jiang et al., 2022) is equivalent
to vanilla Dijkstra’s algorithm when the search nodes are ordered
by the cumulative log probability of the tactic predictions.

                                                                         18
Graph2Tac: Online Representation Learning of Formal Math Concepts




           Figure 9. Cumulative pass rates for all packages.
                                  19
                             Graph2Tac: Online Representation Learning of Formal Math Concepts

I. Informal Comparison on CoqGym Test                                       • Each benchmark may use different versions of test
   Packages                                                                   packages, which includes different (in some cases sig-
                                                                              nificantly different) number of test theorems.
Besides highlighting our novel definition task, our work is
the first work we are aware of comparing k-NN, transformer,
and graph-based solvers for an interactive theorem prover.
                                                                            • The ASTactic/TacTok/Diva family of benchmarks were
Perhaps surprisingly, the online k-NN performs much bet-
                                                                              run for 10 minutes, although TacTok and Diva run
ter than expected, especially since most recent papers use
                                                                              multiple solvers in parallel for a total run time, re-
powerful neural models like transformers.
                                                                              spectively, of 2×10 and 64×10 minutes. Some of
The primary benchmark for Coq is the CoqGym benchmark,                        our benchmarks were run for 5 minutes and some for
consisting of 28 test projects. Unfortunately, of those 28,                   10. ProverBot9001, on the other hand, does not use a
only seven are included in our dataset (our data is harvested                 time limit, instead stopping the search based on search
from Opam packages, while the CoqGym data is retrieved                        depth. Nonetheless, the ProverBot9001 results were
from Github). Of those seven projects, all but one (poltac)                   specifically designed by the creators to compare to the
are included in our training set, making it impossible to do                  ASTactic/TacTok family of benchmarks.
a fair evaluation with any of our trained models. Nonethe-
less, we can compare our trained models on poltac and our
untrained models, such as the online k-NN model, on five                    • There are differences in hardware. ASTactic, for exam-
of the remainder.14                                                           ple, uses two cores, where we restrict ourselves to one
In Tables 2 and 3, we compare our work to two other fam-                      core. Since ProverBot9001 does not use time limits,
ilies of benchmarks on the CoqGym test projects. The                          hardware does not matter.
first family are benchmarks of Yang & Deng (2019), First
et al. (2020), First & Brun (2022), and Sanchez-Stern
                                                                         Nonetheless, the previous CoqGym benchmarks have a sim-
et al. (2023). These include the neural solver ASTac-
                                                                         ilar flavor to ours. All results test on entire packages not
tic and its extensions TacTok, Diva, TacTok+Passport,
                                                                         seen during training. The benchmarks were all run without a
as well as an independent benchmark of CoqHammer.
                                                                         GPU (except our transformer baseline). None of the systems
The second is a benchmark of the neural solver Prover-
                                                                         use large-scale pre-training on internet data, so there is little
bot9001 (Sanchez-Stern et al., 2020). While the origi-
                                                                         risk of data leakage.
nal ProverBot9001 results were for CompCert, we use
data from the ProverBot9001 benchmark found at https:                    The results in Table 2 and Table 3 suggest that the online
//proverbot9001.ucsd.edu/compare/. It is a                               k-NN model, despite being one of the simplest models we
comparison to CoqGym using approximately similar train-                  compare, is one of the strongest. In particular, it outperforms
ing and test packages, but run in the ProverBot9001 system.              the other previously published neural models, only doing
For our family of benchmarks, we include both the trained                worse than ProverBot9001 on one project.
solvers reported in our results section (only tested on poltac),
                                                                         Transitively, this suggests our best G2T models are also
as well as a full 10 minute online k-NN and CoqHammer
                                                                         state of the art for Coq, and we indeed see this on poltac in
benchmark run on all theorems in all six projects.
                                                                         Table 3.
It should be emphasized that these comparisons are informal
                                                                         Finally, note that our CoqHammer combined aggregate
and non-conclusive due to a number of methodological
                                                                         solver performs similarly to the previous benchmark of Coq-
differences:
                                                                         Hammer, suggesting our aggregate is a good approximation
                                                                         (see Section J). Nonetheless, our CoqHammer benchmarks
   • The ASTactic/TacTok/Diva and ProverBot9001 bench-                   and those in CoqGym likely use different versions of Coq-
     marks train on the CoqGym training suite, or in the                 Hammer and likely rely on different combinations of ATP
     case of ProverBot9001 an approximation of the Coq-                  backends.
     Gym training suite, while our G2T models train on our
     training suite containing different Coq projects.                   In conclusion, more work is needed to compare the methods
                                                                         in this paper to other methods in the literature. The strong
   • Coq versions used by the benchmarks vary between                    showing of the online k-NN baseline, which until now has
     version 8.10 and 8.12.                                              not been properly compared to other systems, suggests that
   14                                                                    many of the approaches in the literature, especially the com-
      We excluded goedel as it has completely changed between the
CoqGym benchmarks and ours. It has been abandoned and merged             mon transformer approaches, may be surprisingly weak,
into hydra-battles. Our package of goedel only contains 17% of           especially in the online setting of new files or packages not
the 606 theorems found in the older goedel package in CoqGym.            seen during training.

                                                                    20
                               Graph2Tac: Online Representation Learning of Formal Math Concepts

                        time                                                pass rate (solved/total)
                       (min)     buchberger         coquelicot             hoare-tut        huffman       zorns-lemma             total
 ASTactic           10 0.097 (70/725)            0.065 (95/1467)       0.056 (1/18)     0.080 (25/314)   0.067 (10/149)    0.105 (319/3036)
 CoqHammer          10 0.229 (166/725)           0.186 (273/1467)      0.333 (6/18)     0.236 (74/314)   0.121 (18/149)    0.272 (826/3036)
 Diva            64×10 0.204 (148/725)           0.128 (188/1467)      0.278 (5/18)     0.178 (56/314)   0.121 (18/149)    0.193 (585/3036)
 TacTok           2×10 0.105 (76/725)            0.068 (100/1467)      0.278 (5/18)     0.089 (28/314)   0.081 (12/149)    0.110 (333/3036)
 TacTok+Passport 2×10 0.126 (91/725)             0.082 (120/1467)      0.222 (4/18)     0.096 (30/314)   0.081 (12/149)    0.129 (392/3036)
 ProverBot9001           NA 0.237 (178/750) 0.107 (187/1743) 0.280 (7/25) 0.225 (71/316) 0.115 (18/156) 0.194 (639/3299)
 CH combined              10 0.284 (213/750) 0.148 (258/1743) 0.320 (8/25) 0.207 (65/314) 0.100 (26/259) 0.242 (822/3400)
 kNN-online               10 0.264 (198/750) 0.234 (408/1743) 0.320 (8/25) 0.169 (53/314) 0.282 (73/259) 0.284 (967/3400)

Table 2. Comparison of results across three families of benchmarks. Note each family has a different number of theorems. The total
column includes the poltac results in Table 3. The Diva and TacTok solvers run multiple solvers in parallel, each for 10 minutes.


                                 time pass rate (solved/total)             the Venn diagram in Figure 11, the ATP’s are not nearly
                                (min)          poltac                      as complimentary on our testing set as one would expect.
    ASTactic                      10    0.325       (118/363)              The Vampire backend is able to prove most of the theorems
    CoqHammer                     10    0.796       (289/363)              obtained by other ATP’s. Only the sauto and best tactics
    Diva                       64×10    0.468       (170/363)              remain highly complementary to Vampire. Figure 10 shows
    TacTok                      2×10    0.309       (112/363)              that a combination of best and Vampire produces the same
    TacTok+Passport             2×10    0.372       (135/363)
                                                                           results as an aggregation of all solvers, but faster. As such,
    ProverBot9001                 NA 0.576          (178/309)              unless one truly has CPU-threads to spare for parallel solv-
    CoqHammer combined             10   0.816       (252/309)              ing, using many ATP’s is not effective.
    G2T-Anon-Update                 5   0.864       (267/309)
    G2T-Named-Update                5   0.867       (268/309)              As a result, CoqHammer is no longer able to beat the on-
    G2T-NoDef-Frozen                5   0.773       (239/309)              line k-NN and G2T solver on our testing set. We speculate
    Transformer (GPU)               5   0.560       (173/309)              that the root cause of this discrepancy is the use of a more
    kNN-online                     10   0.735       (227/309)              complex test set, on which the higher-order to first-order
                                                                           translation of CoqHammer is far less effective. Presumably,
Table 3. Comparison of results on poltac, which is in both our test
                                                                           during the development of CoqHammer, the translation was
set and the CoqGym test set, across three families of benchmarks.
                                                                           tuned particularly well on Coq’s standard library. This trans-
                                                                           lation appears to generalize to other packages less well than
                                                                           one would hope.
J. Analysis of CoqHammer Benchmarks
A core design principle of CoqHammer is the ability to
translate a higher-order theory into a first-order theory and
export it to a varied set of automatic theorem provers. Data
provided by the original CoqHammer publication (Czajka &
Kaliszyk, 2018) suggests that the various ATP’s are highly
complementary. Indeed, this is confirmed in a publication
on Tactician (Blaauwbroek et al., 2020a) which compares
an early version of its online k-NN solver with CoqHammer
on Coq’s standard library. The online k-NN solver is able
to beat any of CoqHammer’s individual ATP backends by
some margin. But when combined, the ATP’s achieve a
higher pass-rate than the online k-NN solver.
To obtain a fair comparison, we benchmarked all of Coq-
Hammer’s ATP backends individually. We then calculate
a time-scaled combination of the ATP’s in order to simu-
late the parallel execution of all ATP’s on a single CPU.
Surprisingly, our results are quite different from what is
reported in previous publications.15 As can be seen from                   on Coq’s standard library because CoqHammer depends on the
                                                                           same standard library. This creates a circularity that cannot easily
  15
       Note that we are unable to reproduce the benchmark results          be broken.

                                                                      21
                           Graph2Tac: Online Representation Learning of Formal Math Concepts

                                                                     K. The Relative Speed of the Models




Figure 10. Pass rates for individual solvers of CoqHammer and
various aggregates. (Includes all test packages except hott.)
                                                                     Figure 12. Density plots of the speed of the various models, in
                                                                     tactics executed per second and model calls per second.

                                                                     Figure 12 shows the speed of the models for the attempted
                                                                     proofs in the test set. Notice the various families of models
                                                                     can differ by an order of magnitude in speed, with k-NN
                                                                     models being the fastest, and transformers being the slowest.

                                                                     L. Ablation of k-NN Solvers Seeing Recent
                                                                        Proofs
                                                                     In this section, we explore variations of the k-NN setup.
                                                                     The online and offline k-NN solvers in our main results
                                                                     have multiple differences from each that determine which
                                                                     examples in the global context the k-NN can search over.
                                                                     The online k-NN can search over only the most recent 1000
                                                                     tactics, but can see proofs up to and including those in the
                                                                     current file. The offline k-NN is not restricted to 1000
                                                                     tactics, but can see all the tactics that were available at
                                                                     training time, and uses locality sensitive hashing forests
                                                                     (LSHF) to account for the larger search space.
                                                                     To break down the contribution of each difference, in Ta-
                                                                     ble L, we specify six solvers that vary on two dimensions.
                                                                     The first dimension is how online the model is. The most
                                                                     online models search over proofs up to and including the
                                                                     current file. The next level excludes the current file. The
                                                                     final level excludes all but the training data.
Figure 11. Venn diagram showing complementarity between Coq-
Hammer solvers. (Includes all test packages except hott.)            The second dimension is whether the model only sees the
                                                                     1000 most recent tactics. For proofs in different files, the
                                                                     order of the theorems is someone arbitrary, and this likely

                                                                22
                              Graph2Tac: Online Representation Learning of Formal Math Concepts

               Solver                           Global context proof data           LSHF      Notes
                                            files                     recent
               kNN-recent-online            imports + current file        1000                “online k-NN” in results
               kNN-LSHF-online              imports + current file        all       ✓         k-NN in Tactician
               kNN-recent-allButFile        imports                       1000
               kNN-LSHF-allButFile          imports                       all       ✓
               kNN-recent-offline           imports in training data      1000
               kNN-LSHF-offline             imports in training data      all       ✓         “offline k-NN” in results

                                                  Table 4. k-NN models in the ablation.


affects the results. If we are not restricting to 1000 tactics,         1000 tactics, but where they cannot see the current file.
then we use LSHF to speed up the search.                                This is likely an artifact of the arbitrary way that proofs are
                                                                        ordered outside the current file.
The solver kNN-LSHF-online is the default k-NN solver in
Tactician (Blaauwbroek et al., 2020b). The solvers kNN-                 Overall these results suggest the online k-NN approach may
recent-online and kNN-LSHF-online are the solvers in the                be slightly brittle in that it depends a lot on what recent proof
results section.                                                        data is available in the global context. Nonetheless, given
                                                                        the speed and simplicity of the k-NN solvers, and how even
                                                                        the offline k-NN models have non-negligible performance,
                                                                        we think they are good baseline models for theorem proving.

                                                                        M. Effect of Training Time on G2T Solvers
                                                                        The G2T-Anon model was trained for 247 epochs over 20
                                                                        days. In this section we show that we can achieve compa-
                                                                        rable results with only 27 epochs in 2 days. In table 5 and
                                                                        Figure 15, we see that a model trained for only 27 epochs
                                                                        (the earliest checkpoint we saved) does as well, if not bet-
                                                                        ter, than a model trained for the full 247 epochs, despite
                                                                        the fact that the latter model has better validation accuracy.
                                                                        (Moreover, we found this behavior was consistent across
                                                                        packages.) This is important for the following reasons: (1)
                                                                        Faster model training allows for more rapid development
                                                                        and experimentation. (2) During training, after about 100
                                                                        epochs we regularly encounter instabilities requiring us to
                                                                        restart training from a previous checkpoint. (3) Shorter train-
                                                                        ing time likely means shorter fine-tuning, hopefully making
                                                                        it possible for end users to fine-tune our model on new Coq
Figure 13. Pass rates for the different k-NN solver variations.         projects, even with limited GPU availability.

Figure 13 gives the performance of all six solvers. There
is a significant performance advantage for the full online                    Training Time      Validation    Test
solvers, which can see previous proofs in the same file, and             epochs GPU-hours days loss accuracy pass rate
even a bit more advantage when the model is restricted to                     27           91.5      2 8.65         0.497      0.267
only the most recent 1000 tactics. This suggests that our                    247          907.1     20 8.25         0.567      0.261
online k-NN (kNN-recent-online), gets much of its power
from copying nearby tactics of proofs in the same file.                 Table 5. Statistics for two G2T-Anon checkpoints. Training times
There is also some smaller advantage when going from a                  do not account for the four instances we restarted training from
                                                                        an earlier checkpoint. Validation accuracy is the proportion of
model that can see only the training data to one that can see
                                                                        instances where the generated base tactic plus arguments (using
all but the most recent file. This again shows the importance           greedy decoding) match the ground truth from the held-out valida-
of recent online information.                                           tion set. The pass rate uses the G2T-Anon-Update configuration.
The worst models are the ones restricted to the most ”recent”

                                                                   23
                              Graph2Tac: Online Representation Learning of Formal Math Concepts

                                                                       Also, note that the models with and without name embed-
                                                                       dings have different behaviors when we recalculate all def-
                                                                       inition embeddings including those seen during training.
                                                                       G2T-Named-Recalc shows the same performance as G2T-
                                                                       Named-Update. Recalculating all embeddings would sim-
                                                                       plify the solver interface since one does not have to keep
                                                                       track of which definitions were part of training.
                                                                       However, this is not true of G2T-Anon-Recalc. One possi-
                                                                       ble reason for this discrepancy is that names break symme-
                                                                       tries when calculating definition embeddings from scratch.
                                                                       Isomorphic definitions have isomorphic graphs and hence
                                                                       receive the same embedding by our definition model (if
                                                                       name embeddings are not also used). One example of this is
                                                                       the embeddings for the Boolean values true and false.
                                                                       Further, this symmetry can propagate. If true and false
                                                                       are given the same embedding, then so are the Boolean
                                                                       operations andb and orb since the graph of the former is
                                                                       isomorphic to the latter with true and false swapped.

Figure 14. Pass rates for different checkpoints of G2T-Anon.           O. Additional Combinations with the Online
                                                                          k-NN
N. Ablation of G2T Solvers and Symmetry                                In our main results, we remark on how the online k-NN
   Breaking with Names                                                 solver and the G2T-Anon-Update solver are particularly
                                                                       complimentary. We demonstrated this by plotting the com-
                                                                       bined time-scaled aggregate in Figure 5. This is additionally
                                                                       supported by the Venn diagram in Figure 6 which showed
                                                                       the G2T-Anon-Update model and the online k-NN to be
                                                                       most disjoint.
                                                                       In Figure 16 we further show that of all the solvers, the
                                                                       online k-NN pairs best with the G2T-Anon-Update and G2T-
                                                                       Named-Update models, which both use our novel definition
                                                                       embeddings. This again supports the complementary of the
                                                                       two online approaches, as represented in Figure 1.




Figure 15. Pass rates for the different G2T solver variations.

Figure 15 shows all seven G2T variations mentioned in
Subsection 3.2. In particular, we see that using the frozen
version of a model where the definition task is not used
to compute new definition embeddings hurts model perfor-
mance. This suggests that our definition network is not
just a helpful auxiliary task during training, but an essential
component of our online system.

                                                                  24
                            Graph2Tac: Online Representation Learning of Formal Math Concepts

                                                                       Nonetheless, we do notice a small improvement in the G2T-
                                                                       Anon-Update solver over the G2T-NoDef-Frozen solver
                                                                       in the 0 new dependency setting. This suggests that the
                                                                       definition training task may show some usefulness on its
                                                                       own as an auxiliary task during training even when not used
                                                                       at inference time.
                                                                       The online k-NN solver starts to outperform the G2T mod-
                                                                       els when dependencies get into the hundreds. It is unclear
                                                                       why this happens. In particular, there are many correlations
                                                                       between the number of new dependencies and the package.
                                                                       Larger Coq developments have a larger number of new de-
                                                                       pendencies, but they may support some solvers over others
                                                                       for other orthogonal reasons.

                                                                       Q. Discovery of Inconsistent Axioms
                                                                       After benchmarking our solvers we discovered that three
                                                                       of our test packages contained inconsistent axioms. These
                                                                       axioms are used for development or special logical manipu-
                                                                       lation but are not intended to be used blindly in theorems,
Figure 16. Pass rates of various solvers combined with the k-NN        as they can be used to prove false results.
solver. All combined solvers scale time so that time is evenly
divided among the two component solvers. The uncombined k-             As shown in Table 6, some of our solvers were able to dis-
NN is provided for reference.                                          cover these axioms and use them. The most significant case
                                                                       was skip_axiom in the tlc package. G2T-Anon-Update
                                                                       managed to solve 192 of the 500 test theorems (38.4%) for
                                                                       the 5-minute benchmark using this axiom. Figure 20 shows
P. Impact of the Online Setting                                        the results with all test theorems and when restricting to
                                                                       theorems for which no model used skip_axiom.
An important distinction of our paper is our use of entire
packages for testing, instead of splitting theorems into test          It is impressive that our model was able to discover the
and train randomly as many other papers do.                            importance of this axiom, but it also makes the evaluation
                                                                       of our results difficult. For example, on tlc, the name-less
To investigate this, we measure, for each of our test theo-
                                                                       G2T model significantly outperforms the one with names,
rems, the number of new definition dependencies not seen
                                                                       but mostly because it was able to exploit this axiom.
during training required for that theorem (both in its theorem
statement and proof). This includes transitive dependencies.           The axioms are as follows. In tlc:
Figure 17 shows the number of solved theorems as a func-
tion of new dependencies. Figure 18 shows the per-time                 Axiom skip_axiom : False.
pass rate, conditioned on the number of dependencies. Fig-
ure 19 is the same, but conditioned on the number of model             In hott:
calls.16 In general, having more new dependencies is more
challenging for all the solvers.                                       Inductive No_Empty_for_admitted := .
For 0 new dependencies, we see less difference between all             Axiom No_Empty_admitted
                                                                         : No_Empty_for_admitted.
the solvers, and our best solvers solve over 60% of theorems.
But when we move to a higher number of new dependencies,
the offline models, including the transformer models, the              In haskell:
offline k-NN, and G2T-NoDef-Update, underperform the
online models, the online k-NN, G2T-Anon-Update, and                   Definition undefined {a : Type} : a.
G2T-Named-Update. This is yet more justification that the              Admitted.
main benefit of our definition task and the online k-NN is
their usefulness in online settings.                                   In quickchick (used for training):
  16
    Note that due to discrepancies in how we collect the depen-
dency data, not all test theorems are included in the figures.         Axiom ignore_generator_proofs : False.

                                                                  25
                            Graph2Tac: Online Representation Learning of Formal Math Concepts




Figure 17. Theorems solved as a function of new dependencies. (Smoothed to account for small numbers in each category.) The dotted
line shows the total number of test tactics (also smoothed) as some numbers of dependencies are more common.




                       package     axiom                          solver                    count    percent
                       haskell     undefined                      G2T-Anon-Update               3      1.7%
                       haskell     undefined                      G2T-Named-Update              8      4.6%
                       haskell     undefined                      G2T-NoDef-Frozen             13      7.5%
                       hott        No_Empty_admitted              G2T-Anon-Update               9      1.8%
                       hott        No_Empty_admitted              kNN-online                    2      0.4%
                       tlc         skip_axiom                     G2T-Anon-Update             192     38.4%
                       tlc         skip_axiom                     G2T-Named-Update              5      1.0%
                       tlc         skip_axiom                     G2T-NoDef-Frozen             25      5.0%

         Table 6. The number of times the solvers use inconsistent axioms to prove a test theorem in the 5 minute benchmark.




                                                                 26
        Graph2Tac: Online Representation Learning of Formal Math Concepts




Figure 18. Cumulative pass rates as a function of time, split into four dependency categories.




                                             27
           Graph2Tac: Online Representation Learning of Formal Math Concepts




Figure 19. Cumulative pass rates as a function of model calls, split into four dependency categories.




                                                 28
                              Graph2Tac: Online Representation Learning of Formal Math Concepts




Figure 20. Pass rates on the tlc test theorems. The left plot shows the results on 500 theorems theorems. The right plot restricts to test
theorems not solved using an inconsistent axiom by any of the benchmarked solvers.


R. Examples of Theorems Solved                                          Lemma toZpK n : cancel (@toZp n) (@fromZp n).
                                                                        Proof. case E: (n == 0).
Here we provide illustrative, cherry-picked examples of
how different solvers are able to exploit different types of            Lemma toZp_inj n : injective (@toZp n).
information.                                                            Proof. apply (can_inj (@toZpK _)). Qed.


Using a New Definition in a Theorem In this example                     G2T-Anon-Update          and   G2T-Named-Update         can
from odd-order, the theorem nsKM is in a Coq section and                both solve this theorem with a similar proof:
depends on both the section variable M and a new definition             apply : can_inj. exact : toZpK.,                      some-
K, defined to be the product of the normal groups of M.                 thing neither the offline models or nor the online k-NN was
                                                                        capable of.
Variables M P0 : {group gT}.
Let K := M`_\F%G.                                                       However, the the online k-NN can solve a similar example
                                                                        tiV from bits, because tiV is the third in a list of facts, all
Let nsKM : K <| M.                                                      using the same proof.
Proof. exact: gFnormal. Qed.
                                                                        Let cycW : cyclic W.
G2T-Anon-Update was the only model to find a proof, find-               Proof. by case: ctiW. Qed.
ing the same proof (on its first attempt) as the original using
the lemma gFnormal.                                                     Let oddW : odd #|W|.
                                                                        Proof. by case: ctiW. Qed.
Lemma gFnormal gT (G : {group gT})
  : F gT G <| G.                                                        Let tiV : normedTI V G W.
                                                                        Proof. by case: ctiW. Qed.
One possibility is that G2T-Anon-Update is using the hier-
archical nature of our definition task, as one has to go back           The online k-NN can retrive that tactic by case: ctiW.
a few steps in the definition hierarchy to verify that K fits           since it is in its database of recent proofs. In this case, nei-
the form F gT G used in gFnormal.                                       ther G2T-Anon-Update nor G2T-Named-Update could solve
                                                                        this, nor any of the offline solvers. (However, CoqHammer’s
Using a New Lemma in a Proof In this next example                       best tactic was successful.)
from bits, the lemma toZp_inj uses the immediately pre-
ceding new lemma toZpK, which was not seen during train-                Using New Tactics The online k-NN can also find and
ing.                                                                    use new tactics, something none of the other solvers can do.

                                                                   29
                           Graph2Tac: Online Representation Learning of Formal Math Concepts

The package hott is very different from the training data,            S. Patterns in the Definition Embeddings
often using custom tactics, like the tactic make_equiv
used in the proof of equiv_sigma_assoc'.                              Our three models—G2T-Anon, G2T-Named, and G2T-
                                                                      NoDef—take different approaches in training the learned
Definition equiv_sigma_assoc'                                         definition embeddings. In Figures 21, 22, and 23 we show
  `(P : A -> Type)                                                    UMAP representations of the learned definition embed-
  (Q : forall a : A, P a -> Type)                                     dings.
  : {a : A & {p : P a & Q a p}}
    <˜> {ap : sig P & Q ap.1 ap.2}.                                   Overall we see that G2T-Anon and G2T-Named have a more
Proof.                                                                intricate structure. Since G2T-Anon does not have access
  make_equiv.                                                         to names, the embeddings are more focused on structure,
Defined.
                                                                      including the top-level structure of what type of definition it
It was easy for the online k-NN to find this proof as most            is.
theorems in this file used the same tactic, while none of the         It is not clear what the major clusters of the G2T-Named
other solvers could solve this.                                       model are, although we can determine it is not just related
                                                                      to easy-to-identify features of the name or the definition, but
Predicting Tactics with Terms While the transformer                   instead seems to be a combination of multiple factors.
model rarely solved a proof that the wasn’t also solvable by
the G2T models, there is an interesting example from hott.            As for the G2T-NoDef, since there is no definition task, the
The proof of meet_lb_3_assoc_m relies on construct-                   only signal used to train the embedding is how the definition
ing the term y ⊔ z, something that, of all the machine-               is used, either as a node in a proof state or as an argument to
learned solvers in this paper, only the transformer is capable        a tactic. The center seems to be almost exclusively made up
of.                                                                   of non-theorem definitions. Further, we have noticed at least
                                                                      some of the radial clusters are associated with particular
Lemma meet_lb_3_assoc_m x y z                                         tactics. For example, we found a cluster almost exclusively
  : x ⊔ (y ⊔ z) ≤ y.                                                  made up of definitions used as an argument to rewrite _.
Proof.
transitivity (y ⊔ z).
- apply meet_lb_r.
- apply meet_lb_l.
Qed.

(This theorem was also proved by the firstorder tactic.)

Using Name Information Last, in tlc, consider the theo-
rem LibListZ.length_map.

Lemma length_map :
  forall A B (l:list A) (f:A->B),
  length (map f l) = length l.
Proof using.
  intros. unfold length. rewrite˜ length_map.
Qed.

Note,  the  proof  of              this    theorem      calls
LibList.length_map:

Lemma length_map : forall f l,
  length (map f l) = length l.

While it looks like these two theorems says the exact
same thing, the first theorem uses LibListZ.length
which gives an integer length while the second uses
LibList.length which gives a natural number length.
Because G2T-Named-Update can see the name of the def-
initions, it had an advantage over G2T-Anon-Update in
this case and was able to solve LibListZ.length_map
with a similar proof, while G2T-Anon-Update did not.

                                                                 30
                              Graph2Tac: Online Representation Learning of Formal Math Concepts




Figure 21. UMAP representations of learned definition embeddings colored by definition type. The G2T-Anon embeddings are clustered
between tactical constants (mostly theorems with tactical proofs), manual constants (definitions defined via terms), and inductively defined
definitions. (Projections in record types are relatively rare.) Manual and tactical constants are less separated in G2T-Named, but inductive
definitions still do not mix. Manual constants make up a significant portion of the center cluster of the G2T-NoDef embeddings.




Figure 22. UMAP representations of learned definition embeddings colored by whether the definition was used as an argument of a tactic.
All the model definition embeddings take this dimension into account. This makes sense since argument selection is an important part of
tactic prediction.




Figure 23. UMAP representations of learned definition embeddings restricted to definitions whose qualified names start with mathcomp
colored by the second part of the name after mathcomp, e.g. mathcomp.algebra.matrix.Matrix. The G2T-Named model
clusters more by these categories, whereas in the G2T-Anon they show as smoothed-out bands.


                                                                    31
