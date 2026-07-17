                                                                          Coming to Terms with Quantified Reasoning

                                                             Laura Kovács                                                                Simon Robillard                                    Andrei Voronkov
                                                         TU Wien, Austria                                                Chalmers Univ. of Technology, Sweden                         University of Manchester, UK
                                                    laura.kovacs@tuwien.ac.at                                                simon.robillard@chalmers.se                          Chalmers Univ. of Technology, Sweden
                                                                                                                                                                                         andrei@voronkov.com




                                        Abstract
arXiv:1611.02908v1 [cs.LO] 9 Nov 2016




                                                                                                                                                        program analysis. Terms may be used to formalize the semantics
                                        The theory of finite term algebras provides a natural framework to                                              of programming languages (Goguen et al. 1977; Clark 1978; Cour-
                                        describe the semantics of functional languages. The ability to effi-                                            celle 1983); they can also themselves be the object of computation.
                                        ciently reason about term algebras is essential to automate program                                             The latter is especially obvious in the case of functional program-
                                        analysis and verification for functional or imperative programs over                                            ming languages, where algebraic data structures are manipulated.
                                        algebraic data types such as lists and trees. However, as the theory                                            Consider for example the following declaration, in the functional
                                        of finite term algebras is not finitely axiomatizable, reasoning about                                          language ML:
                                        quantified properties over term algebras is challenging.                                                                datatype nat = zero | succ of nat;
                                            In this paper we address full first-order reasoning about prop-
                                        erties of programs manipulating term algebras, and describe two                                                 Although the functional programmer calls this a data type declara-
                                        approaches for doing so by using first-order theorem proving. Our                                               tion, the logician really sees the declaration of an (initial) algebra
                                        first method is a conservative extension of the theory of term alge-                                            whose signature is composed of two symbols: the constant zero
                                        bras using a finite number of statements, while our second method                                               and the unary function succ. The elements of this data type/algebra
                                        relies on extending the superposition calculus of first-order theorem                                           are all ground (variable-free) terms over this signature, and pro-
                                        provers with additional inference rules.                                                                        grams manipulating terms of this type can be declared by means of
                                            We implemented our work in the first-order theorem prover                                                   recursive equations. For example, one can define a program com-
                                        Vampire and evaluated it on a large number of algebraic data type                                               puting the addition of two natural numbers by the following two
                                        benchmarks, as well as game theory constraints. Our experimental                                                equations:
                                        results show that our methods are able to find proofs for many hard                                                       add zero x = x
                                        problems previously unsolved by state-of-the-art methods. We also
                                                                                                                                                                  add (succ x) y = succ (add x y)
                                        show that Vampire implementing our methods outperforms existing
                                        SMT solvers able to deal with algebraic data types.                                                             Verifying the correctness of programs manipulating this data type
                                                                                                                                                        usually amounts to proving the satisfiability of a (possibly quanti-
                                        Categories and Subject Descriptors CR-number [subcategory]:
                                                                                                                                                        fied) formula in the theory of this term algebra. In the case of the
                                        D 2.4 Software/Program Verification, F.3.1 Specifying and Ver-
                                                                                                                                                        program defined above, a simple property that one might want to
                                        ifying and Reasoning about Programs, F.3.2 Semantics of Pro-
                                                                                                                                                        check is that adding a non-zero natural number to another results in
                                        gramming Languages, F 4.1. Mathematical Logic, I.2.3 Deduc-
                                                                                                                                                        a number that is also different from zero:
                                        tion and Theorem Proving, I.2.4 Knowledge Representation For-
                                        malisms and Methods                                                                                                  x 6= zero ∨ y 6= zero ⇒ add x y 6= zero
                                        Keywords Program analysis and verification, algebraic data types,                                               Note that depending on the semantics of the programming lan-
                                        automated reasoning, first-order theorem proving, superposition                                                 guage, there may exist cyclic terms such as the one satisfying the
                                        proving                                                                                                         equation x ≈ succ(x), or even infinite terms, but in a strictly evalu-
                                                                                                                                                        ated language, only finite non-cyclic terms lead to terminating pro-
                                        1.      Introduction                                                                                            grams. Since program verification is in general concerned with pro-
                                                                                                                                                        gram safety and termination, it is desirable to consider in particular
                                        Applications of program analysis and verification often require                                                 the theory of finite term algebras, denoted by TF T in the sequel.
                                        generating and proving properties about algebraic data types, such                                                  The full first-order fragment of TF T is known to be decid-
                                        as lists and trees. These data types (sometimes also called recur-                                              able (Mal’cev 1962). One may hence hope to easily automate the
                                        sive or inductive data types) are special cases of term algebras, and                                           process of reasoning about properties of programs manipulating al-
                                        hence reasoning about such program properties requires proving in                                               gebraic data types, such as lists and trees, corresponding to term
                                        the first-order theory of term algebras. Term algebras are of partic-                                           algebras. However, properties of such programs are not confined
                                        ular importance for many areas of computer science, in particular                                               strictly to TF T for the following reasons: program properties typi-
                                                                                                                                                        cally include arbitrary function and predicate symbols used in the
                                                                                                                                                        program, and they may also involve other theories, for example
                                                                                                                                                        the theory of integer/real arithmetic. Decidability of TF T is how-
                                                                                                                                                        ever restricted to formulas that only contain term algebra symbols,
                                                                                                                                                        that is, uninterpreted functions, predicates and other theory sym-
                                                                                                                                                        bols cannot be used. If this is not the case, non-linear arithmetic
                                                                                                                                                        could trivially be encoded in TF T , implying thus the undecidabil-
                                                                                                                                                        ity of TF T . Due to the decidability requirements of TF T on the
                                        To appear in Proceedings of the 44th ACM SIGPLAN Symposium on Principles of Programming Languages. ACM, 2017.   one hand, and the logical structure of general program properties
over term algebras on the other hand, decision procedures based                 an important consequence of this conservative extension, our
on (Mal’cev 1962) for reasoning about programs manipulating al-                 work yields a superposition-based decision procedure for term
gebraic data cannot be simply used. For the purpose of proving                  algebras (Section 5).
program properties with symbols from TF T , one needs more so-              • We show how to optimize superposition-based first-order rea-
phisticated reasoning procedures in extensions of TF T .                        soning using new, term algebra specific, simplification rules,
    For this purpose, the works of (Barrett et al. 2007; Reynolds and           and an incomplete, but simple, replacement for a troublesome
Blanchette 2015) introduced decision procedures for various frag-               acyclicity axiom. Our new inference system provides an alter-
ments of the theory of term algebras; these techniques are imple-               native and efficient approach to axiomatic reasoning about term
mented as satisfiability modulo theory (SMT) procedures, in par-                algebras in first-order theorem proving and can be used with
ticular in the CVC4 SMT solver (Barrett et al. 2011). However,                  combinations of theories (Section 6).
these results target mostly reasoning in quantifier-free fragments
of term algebras. To address this challenge and provide efficient           • We implement our work in the first-order theorem prover Vam-
reasoning techniques with both quantifiers and term algebra sym-                pire. Our works turns Vampire into the first first-order theo-
bols, in this paper we propose to use first-order theorem provers.              rem prover able to reason about term algebras, and therefore
We describe various extensions of the superposition calculus used               about algebraic data types. Our experiments show that our im-
by first-order theorem provers and adapt the saturation algorithm of            plementation outperforms state-of-the-art SMT solvers able to
theorem provers used for proof search.                                          reason with algebraic data types. For example, Vampire solved
    Theory-specific reasoning in saturation-based theorem provers               50 SMTLIB problems that could not be solved by any other
is typically conducted by including the theory axioms in the set of             solver before (Section 7).
input formulas to be saturated. Unfortunately a complete axiomati-
zation of the theory of term algebras requires an infinite number of       2.    Preliminaries
sentences: the acyclicity rule, which ensures that a model does not
include cyclic terms, is described by an infinite number of inequal-       We consider standard first-order predicate logic with equality. The
ities x 6≈ f (x), x 6≈ f (f (x)), . . . This property of term algebras     equality symbol is denoted by ≈. We allow all standard boolean
prevents us from performing theory reasoning in saturation-based           connectives and quantifiers in the language. We assume that the
proving in the usual way.                                                  language contains the logical constants > for always true and ⊥
    As a first attempt to remedy this state of affairs, in this paper we   for always false formulas.
present a conservative extension of the theory of term algebras that           Throughout this paper, we denote terms by r, s, u, t, variables
uses a finite number of sentences (Section 5). This extension relies       by x, y, z, constants by a, b, c, d, function symbols by f, g and
on the addition of a predicate to describe the “proper subterm”            predicate symbols by p, q, all possibly with indices. We consider
relation between terms. This approach is complete and can easily           equality ≈ as part of the language, that is, equality is not a symbol.
be used in any first-order theorem prover without any modification.        For simplicity, we write s 6≈ t for the formula ¬(s ≈ t).
    Unfortunately, the subterm relation is transitive, so that the num-        An atom is an equality or a formula of the form p(t1 , . . . , tn ),
ber of predicates produced by saturation quickly becomes a burden          where p is a predicate symbol and t1 , . . . , tn are terms. A literal
for any prover. To improve the efficiency of the reasoning, we of-         is an atom A or its negation ¬A. Literals that are atoms are called
fer an alternative solution: extending the inference system of the         positive, while literals of the form ¬A are negative. A clause is a
saturation theorem prover with additional rules to treat equalities        disjunction of literals L1 ∨ . . . ∨ Ln , where n ≥ 0. When n = 0,
between terms (Section 6).                                                 we will speak of the empty clause, denoted by . The empty clause
    We implemented our new inference system, as well as the sub-           is always false.
term relation, in the first-order theorem prover Vampire (Kovács               We denote atoms by A, literals by L, clauses by C, D, and
and Voronkov 2013). We tested our implementation on two sets               formulas by F, G, possibly with indices.
of benchmarks. We used 4170 problems describing properties of                  Let F be a formula with free variables x̄, then ∀F (respectively,
functional programs manipulating algebraic data types; these prob-         ∃F ) denotes the formula (∀x̄)F (respectively, (∃x̄)F ). A formula
lems were taken from (Reynolds and Blanchette 2015). This set              is called closed, or a sentence, if it has no free variables. A formula
of examples were generated using the Isabelle inductive theorem            or a term is called ground if it has no occurrences of variables.
prover (Nipkow et al. 2002) and translated by the Sledgeham-                   A signature is any finite set of symbols. The signature of a
mer system (Blanchette et al. 2013). Further, we also used prob-           formula F is the set of all symbols occurring in this formula. For
lems from (Colmerauer et al. 2000) with many quantifier alterna-           example, the signature of (∀x)b ≈ g(x) is {g, b}. When we speak
tions over term algebras. When compared to state-of-the-art SMT            about a theory, we either mean a set of all logical consequences
solvers, such as CVC4 and Z3 (de Moura and Bjørner 2008), our              of a set of formulas (called axioms of this theory), or a set of all
experimental results give practical evidence of the efficiency and         formulas valid on a class of first-order structures. Specifically, we
logical strength of our work: many hard problems that could not be         are interested in the theories of term algebras, in which case we use
solved before by any existing technique can now be solved by our           the second meaning. When we discuss a theory, we call symbols
work (see Section 7).                                                      occurring in the signature of the theory interpreted, and all other
Contributions. The main contributions of our paper are summa-              symbols uninterpreted.
rized below.                                                                   By an expression E we mean a term, atom, literal, or clause.
                                                                           A substitution θ is a finite mapping from variables to terms. An
                                                                           application of this substitution to an expression (e.g. a term or a
 • We extend the theory TF T of finite term algebras with a subterm        clause) E, denoted by Eθ, is the expression obtained from E by the
   relation denoting proper subterm relations between terms. We            simultaneous replacement of each variable x in it, such that θ(x)
   call this extension TF+T and prove that TF+T is a conservative          is defined, by θ(x). We write E[s] to mean an expression E with
   extension of TF T . When compared to TF T , the advantage of            a particular occurrence of a term s. A unifier of two expressions
   TF+T is that it is finitely axiomatizable and hence can be used         E1 and E2 is a substitution θ such that E1 θ = E2 θ. It is known
   by any first-order theorem prover. Moreover, one can combine            that if two expressions have a unifier, then they have a so-called
   TF+T with other theories, going even to undecidable fragments           most general unifier (mgu) – see (Robinson 1965) for details on
   of the combined theory of term algebras and other theories. As          computing mgus.
3.    Superposition and Proof Search                                      selection strategy must be fair: every possible inference must be
We now recall some terminology related to inference systems and           selected at some step of the algorithm. A saturation algorithm
first-order theorem proving. Inference systems are used in the the-       with a fair inference selection strategy is called a fair saturation
ory of superposition (Nieuwenhuis and Rubio 2001) implemented             algorithm.
by several leading automated first-order theorem provers, including           A naive implementation of fair saturation algorithms based on S
Vampire (Kovács and Voronkov 2013) and E (Schulz 2002). The               will not yield however an efficient theorem prover. This is because
material of this section is based on (Kovács and Voronkov 2013),          at every step of the saturation algorithm, the number of clauses in
adapted to our setting.                                                   the set S of clauses, representing the proof-search space, grows.
                                                                          Therefore, for the efficiency of organizing proof search, one needs
3.1   The Superposition Inference System                                  to use the notion of redundancy, which allows to delete so-called
                                                                          redundant clauses during saturation from the search space. A clause
First-order theorem provers perform inferences on clauses. An in-         C ∈ S is redundant in S if it is a logical consequence of those
ference rule is an n-ary relation on formulas, where n ≥ 0. The           clauses in S that are strictly smaller than C w.r.t. the simplification
elements of such a relation are called inferences and usually writ-       ordering . In a nutshell, saturation algorithms using redundancy
ten as:                                                                   not only generate but also delete clauses from the set S of clauses.
                            C1 . . . Cn .                                 Deletion of redundant clauses is desirable since every deletion
                                  C                                       reduces the search space. If a newly generated clause C 0 during one
The clauses C1 , . . . , Cn are called the premises of this inference,    step of saturation makes some clauses in S redundant, adding C 0 to
whereas the clause C is the conclusion of the inference. An infer-        the search space will remove other (more complex) clauses from S.
ence system I is a set of inference rules. An axiom of an inference       This observation is exploited by first-order theorem provers in the
system is any conclusion of an inference with 0 premises. Any in-         process of prioritizing inferences during inference selection, giving
ferences with 0 premises and a conclusion C will be written with-         rise to so-called simplifying and generating inferences. Simplifying
out the bar line, simply as C.                                            inferences make one or more clauses in the search space redundant
    Modern first-order theorem provers use and implement the su-          and thus delete clauses from the search space. That is, an inference
perposition inference system, which is parametrized by a simplifi-                                   C1 . . . Cn .
cation ordering  on terms and a selection function on clauses.                                            C
    An ordering  on terms is called a simplification ordering if it
satisfies the following conditions:                                       is called simplifying if at least one of the premises Ci becomes
                                                                          redundant (and deleted) after the addition of the conclusion C to
1.  is well-founded: there exists no infinite sequence of terms          the search space. Inferences that are not simplifying are generating:
   t0 , t1 , . . . such that t0  t1  . . .;                             instead of simplifying clauses in the search space, they generate and
2.  is stable under substitution: if s  t then sθ ≺ tθ, for every       add a new clause to the search space. Efficient saturation algorithms
   term s, t and substitution θ;                                          exploit simplifying and generating inferences, as follows: from
3.  is monotonic: if s  t then l[s]  l[t] for all terms l, s, t;       time to time provers try to search for simplifying inferences at the
                                                                          expense of delaying generating inferences.
4.  has the subterm property: if s is a proper subterm of t, then
   s  t.                                                                 4.    The Theory of Finite Term Algebras
Given two terms s  t, we say that s is smaller than t and t is           A definition of the first-order theory of term algebras over a finite
larger/greater than s wrt . This ordering  can be extended to           signature can be found in e.g. (Rybina and Voronkov 2001), along
literals and clauses.                                                     with an axiomatization of this theory and a proof of its complete-
    A selection function selects in every non-empty clause a non-         ness. In this section we overview this theory and known results
empty subset of literals. In the following, we underline literals to      about it.
indicate that they are selected in a clause; that is we write L ∨ C
to denote that the literal L is selected. A selection function is said    4.1   Definition
to be well-behaved if in a given clause it selects either a negative      Let Σ be a finite set of function symbols containing at least one
literal or all the maximal literals wrt the simplification ordering .    constant. Denote by T (Σ) the set of all ground terms built from
    We now fix a simplification ordering  and a well-behaved             the symbols in Σ.
selection function and define the superposition inference system.             The Σ-term algebra is the algebraic structure whose carrier set
This inference system, denoted by S, consists of the inference rules      is T (Σ) and defined in such a way that every ground term is in-
of Figure 1. The inference system S is a sound and refutationally         terpreted by itself (we leave details to the reader). We will some-
complete inference system for first-order logic with equality. By         times consider extensions of term algebras by additional symbols.
refutational completeness we mean that if a set S of formulas is          Elements of Σ will be called term constructors (or simply just con-
unsatisfiable, then  is derivable from S in S.                           structors), to distinguish them from other function symbols. The
3.2   Proof Search by Saturation                                          Σ-term algebra will also be denoted by T (Σ).
                                                                              Consider the following set of formulas.
Superposition theorem provers implement proof-search algorithms
in S using so-called saturation algorithms, as follows. Given a set                                _
                                                                                                          ∃y (x ≈ f (y))                   (A1)
S of formulas, superposition-based theorem provers try to saturate
                                                                                                   f ∈Σ
S with respect to S, that is build a set of formulas that contains
S and is closed under inferences in S. At every step, a saturation                                   f (x) 6≈ g(y)                         (A2)
algorithm selects an inference of S, applies this inference to S,
                                                                          for every f, g ∈ Σ such that f 6= g;
and adds conclusions of the inferences to the set S. If at some
moment the empty clause  is obtained, by soundness of S, we can
conclude that the input set of clauses is unsatisfiable. To ensure that                        f (x) ≈ f (y) → x ≈ y                       (A3)
a saturation algorithm preserves completeness of S, the inference         for every f ∈ Σ of arity ≥ 1;
 • Resolution
                                               A ∨ C1       ¬A0 ∨ C2                            s 6≈ s0 ∨ C
                                                    (C1 ∨ C2 )σ                                    Cθ
      where A is not an equality predicate, σ = mgu(A, A0 ) and θ = mgu(s, s0 )
 • Superposition

                  l ≈ r ∨ C1         L[l0 ] ∨ C2          l ≈ r ∨ C1         t[l0 ] ≈ t0 ∨ C2           l ≈ r ∨ C1          t[l0 ] 6≈ t0 ∨ C2
                       (C1 ∨ L[r] ∨ C2 )θ                      (C1 ∨ t[r] ≈ t0 ∨ C2 )θ                         (C1 ∨ t[r] 6≈ t0 ∨ C2 )θ
      where l0 not a variable, L is not an equality, θ = mgu(l, l0 ), lθ  rθ and t[l0 ]θ  t0 θ
 • Factoring
                                                   A ∨ A0 ∨ C                     s ≈ t ∨ s0 ≈ t0 ∨ C
                                                    (A ∨ C)σ                     (s ≈ t ∨ t 6≈ t0 ∨ C)θ
      where σ = mgu(A, A0 ), θ = mgu(s, s0 ), sθ  tθ and tθ  t0 θ

                                                      Figure 1. The superposition calculus S.


                                                                               if a formula G is implied by an infinite set of formulas, it is also im-
                                  t 6≈ x                           (A4)        plied by a finite subset of this set. One of contributions of this paper
                                                                               is showing how to avoid dealing with infinite axiomatizations.
for every non-variable term t in which x appears.                                  Further, the non-elementary property of TF T in Theorem 1
    Some of these formulas contain free variables, we assume that              follows from a result in (Ferrante and Rackoff 1979): every theory
they are implicitly universally quantified.                                    in which one can express a pairing function has a hereditarily non-
    Axiom (A1), sometimes called the domain closure axiom, as-                 elementary first-order theory.
serts that every element in Σ is obtained by applying a term con-                  Note that the completeness of TF T implies that TF T is exactly
structor to other elements.                                                    the set of all formulas true in the Σ-term algebra. First-order theo-
    Axiom (A3) describes the injectivity of term constructors, while           ries of term algebras are closely related to non-recursive logic pro-
axiom (A2) expresses the fact that terms constructed from different            grams, for related complexity results, also including the case with
constructors are distinct. Throughout this paper, we refer to (A2) as          only unary functions, see (Vorobyov and Voronkov 1998).
the distinctness axiom and to (A3) as the injectivity axiom.                       Let us make the following important observation. The decidabil-
    The axiom schema (A4), called the acyclicity axiom, asserts that           ity and other results of Theorem 1 do not hold when uninterpreted
no term is equal to its proper subterm, or in other words that there           functions or predicates are added to TF T . If we add to the Σ-term
exist no cyclic terms.                                                         algebra uninterpreted symbols, one can for example use these sym-
    In the following sections we will also discuss theories in which           bols to provide recursive definitions of addition and multiplication,
there are non-constructor function symbols. Note that when we deal             thus encoding first-order Peano arithmetic. Using the same reason-
with such theories, the acyclicity axioms are used only when all               ing as in (Korovin and Voronkov 2007) one can then prove the fol-
symbols in t are constructors.                                                 lowing result.
4.2     Known Results                                                          Theorem 2. The first-order theory of Σ-algebras with uninter-
                                                                               preted symbols is Π11 -complete, when Σ contains at least one non-
We denote by TF T the theory axiomatized by (A1)–(A4), that is,                constant.
the set of logical consequences of all formulas in (A1)–(A4). Note
that the Σ-term algebra is a model of all formulas (A1)–(A4), and                  We will not give a full proof of Theorem 2 but refer to (Korovin
therefore also a model of TF T .                                               and Voronkov 2007) for details. Here, we only show how to encode
                                                                               non-linear arithmetic in TF T using Σ-term algebra uninterpreted
Theorem 1. The following results hold.                                         symbol, which is relatively straightforward. Assume, without loss
1. TF T is complete. That is, for every sentence F in the language             of generality, that Σ contains a constant 0 and a unary function
   of T (Σ), either F ∈ TF T or (¬F ) ∈ TF T .                                 symbol s (successor). Then all ground terms, and hence all term
                                                                               algebra elements are of the form sn (0), where n ≥ 0. We will
2. TF T is decidable.
                                                                               identify any such term sn (0) with the non-negative integer n.
3. If Σ contains at least one symbol of arity > 1, then the first-                 Add two uninterpreted functions + and · and consider the set A
   order theory of TF T is non-elementary.                                     of formulas defined as follows:
    Completeness of TF T is proved in a number of papers - a
detailed proof can be found in, e.g., (Rybina and Voronkov 2001).                                             ∀x (x + 0 = x)
    Decidability of TF T in Theorem 1 is implied by the complete-
ness of TF T and by the fact that TF T has a recursive axiomati-                                    ∀x∀y (s(x) + y = s(x + y))
zation. More precisely, completeness gives the following (slightly
unusual) decision procedure: given a sentence F , run any complete
first-order theorem proving procedure (e.g., a complete superposi-                                            ∀x (x · 0 = 0)
tion theorem prover) simultaneously and separately on F and ¬F .
We can get around the problem that the axiomatisation is infinite                                 ∀x∀y (s(x) · y = (x · y) + y)
but throwing in axioms, one after one, while running the proof                     It is not hard to argue that in any extension of the Σ-algebra
search — indeed, by the compactness property of first-order logic,             satisfying A, the functions + and · are interpreted as the addition
and multiplication on non-negative integers. Let now G be any
sentence using only +, ·, s, 0. Then we have that A → G is valid                          Sub(xi , f (x1 , . . . , xi , . . . , xn )), (B1)
in the Σ-algebra if and only if G is a true formula of arithmetic.
                                                                          for every f ∈ Σ of arity n ≥ 1 and every i such that n ≥ i ≥ 1.
    Note that Theorem 2 refers to the theory of algebras, i.e. the
set of formulas valid on Σ-algebra. In view of this theorem, with
uninterpreted symbols of arity ≥ 1 in the signature, this includes                       Sub(x, y) ∧ Sub(y, z) → Sub(x, z)                  (B2)
more formulas than the set of formulas derivable from (A1)–(A4).
                                                                                                       ¬Sub(x, x)                         (B3)
4.3     Other Formalizations
                                                                             Intuitively, the predicate Sub(s, t) holds iff s is a proper sub-
Instead of using existential quantifiers in (A1), one can also use ax-    term of t. Axiom (B1) ensures that this relation holds for terms
ioms based on destructors (or projection functions) of the algebra.       s appearing directly under a term algebra constructor in t , while
For all function symbols f of arity n > 0 and all i = 1, . . . , n, in-   (B2) describes the transitivity of the subterm relation and ensures
troduce a function pif . The destructor axioms using these functions      that the relation also holds if s is more deeply nested in t. Axiom
are:                                                                      (B3) asserts that no term may be equal to its own proper subterm.
                                                                             We now observe the following properties of (B1)–(B3).
                   x ≈ f (p1f (x), . . . , pn
                                            f (x)).        (A1’)          Theorem 3. TF+T is a conservative extension of TF T , that is:
   The axiom (A3) can be replaced by the following axioms, which
can be considered as a definition of destructors:                         1. Every theorem in TF T is a theorem in TF+T ;
                                                                          2. Every theorem in TF+T that uses only symbols from the language
                 pif (f (x1 , . . . , xi , . . . , xn )) ≈ xi    (A3’)       of TF T (i.e. not using the predicate Sub) is also a theorem of
Given the other axioms, (A3) and (A3’) are logically equivalent, but         TF T .
some authors prefer the presentation based on destructors. Note,          Proof. For (1), it is enough to prove that every instance of the
however, that the behavior of a destructors pif is unspecified on         acyclicity axiom (A4) of TF T is implied by axioms of TF+T . To this
some terms.                                                               end, note that for every term t and its proper subterm s, (B1)–(B2)
                                                                          imply Sub(s, t), so every instance of the acyclicity axiom (A4) is
4.4     Extension to Many-Sorted Logic
                                                                          implied by (B1)–(B3).
In practice, it can be useful to consider multiple sorts, especially          To prove part (2), first note that TF+T is consistent (sound). This
for problems taken from functional programming. In this setting,          follows from the fact that it has a model, which extends the Σ-term
each term algebra constructor has a type τ1 × · · · × τn → τ .            algebra by interpreting Sub as the subterm relation. Now assume,
The requirement that there is at least one constant should then           by contradiction, that there is a sentence F not using Sub such that
be replaced by the requirement that for every sort, there exists a        F ∈ TF+T and F 6∈ TF T . By the completeness result of Theorem 1,
ground term of this sort.                                                 we then have ¬F ∈ TF T , which by part (1) implies ¬F ∈ TF+T .
   We can also consider similar theories, which mix constructor           We have both F ∈ TF+T and ¬F ∈ TF+T , which contradicts the
and non-constructor sorts. That is, some sorts contain constructors       consistency of TF+T .
and some do not.
   Consider an example with the following term algebra signature:             Note that the full first-order theory of term algebras with the
      ΣBin = {leaf : τ → Bin, node : Bin × τ × Bin → Bin}                 subterm predicate is undecidable (Venkataraman 1987).
                                                                              The important difference between TF T and TF+T is that TF+T
This signature defines an algebra of binary trees, where every node       is finitely axiomatizable. This fact and Theorem 3 can be directly
and leaf is decorated by an element of a (non-constructor) sort τ .       used to design superposition-based proof procedures for TF T , as
In this case term algebra axioms are only using sorts with construc-      follows. Given a term algebra sentence F , we can search for a
tors. The axioms of this theory of trees, as defined previously, are      superposition proof of F from the axioms of TF+T . Such a proof
shown in Figure 2.                                                        exists if and only if F holds in the Σ-term algebra. This proof
                                                                          procedure can even be turned into a superposition-based decision
5.     A Conservative Extension of the Theory of                          procedure for TF T , which is based on attempting to prove F and
                                                                          ¬F in parallel, until one of them is proved, which is guaranteed by
       Term Algebras                                                      the completeness of TF T from Theorem 1.
In this paper we aim to prove theorems in first-order theories                It is interesting that, while proving a formula F with quanti-
containing constructor-defined types. While in general the theory         fier alternations in this way, first-order theorem provers will first
is Π11 -complete, we still want to have a method that behaves well in     skolemize F , introducing uninterpreted functions. While the first-
practice. Our method will be based on extending the superposition         order theory of term algebras with arbitrary uninterpreted func-
calculus by axioms and/or rules for dealing with term algebra             tions is incomplete, our results guarantee completeness on formu-
constructor symbols.                                                      las with uninterpreted functions obtained by skolemization. This is
    One of the criteria of behaving well in practice is to have a         so because skolemization preserves validity and hence, using The-
method that is complete for pure term algebra formulas, that is,          orem 3, we conclude completeness on skolemized formulas with
without uninterpreted functions. The immediate idea would be to           uninterpreted functions.
use the axiomatization of term algebras consisting of (A1)–(A4),              While it is hard to expect that proving term algebra formulas
however this does not work since there is an infinite number of           by superposition will result in a better decision procedure com-
acyclicity axioms.                                                        pared to those described in the literature, see e.g. (Colmerauer et al.
    In this section we show how to overcome this problem by using         2000), our approach has the advantage that it can be combined with
an extension of term algebras by a binary relation Sub, denoting          other theories and can be used for proving formulas in undecidable
the proper subterm relation. Let us further denote by TF+T the set        fragments of the full first-order theory of term algebras. Given a
of formulas which contains (A1)–(A3), but replaces the acyclicity         formula containing both constructors, uninterpreted symbols and
axiom (A4) by the following axioms (B1)–(B3):                             possible theory symbols, we can attempt to prove this formula by
                                                                                                  
                                           ∃y x ≈ leaf (y) ∨ ∃y1 , y2 , y3 x ≈ node(y1 , y2 , y3 )

                                                         node(x1 , x2 , x3 ) 6≈ leaf (y1 )

                                                         leaf (x) ≈ leaf (y) → x ≈ y

                                  node(x1 , x2 , x3 ) ≈ node(y1 , y2 , y3 ) → x1 ≈ y1 ∧ x2 ≈ y2 ∧ x3 ≈ y3

                       x 6≈ node(x, y1 , y2 )    x 6≈ node(y1 , y2 , x)      x 6≈ node(node(x, y1 , y2 ), y3 , y4 )          ...

                                   Figure 2. The instantiation of the theory axioms for the signature ΣBin .


adding the axioms of TF+T and then use a superposition theorem               are no inferences that can be done between these clauses (assuming
prover. The results of this section show that this method is strong          we are using the standard Knuth-Bendix ordering).
enough to prove all (pure) term algebra theorems. Our experimen-                 Another example showing that the acyclicity axiom can be hard
tal results described in Section 7 give an evidence that it is also          to drop or replace is the set of two ground unit clauses f (a) ≈ b and
efficient in practice.                                                       f (b) ≈ a, where f is a constructor. This set of clauses is also unsat-
    The conservative extension TF+T presented above thus allows              isfiable in the theory of term algebras, since it implies f (f (b)) = b.
one to encode problems in the theory of term algebras and reason             Similar to the previous example, there is no superposition inference
about them using any tool for automated reasoning in first-order             between these two clauses.
logic. However the transitive nature of the predicate Sub can impact
the performance of provers negatively. Note that the transitivity            6.2   The Distinctness Rule
axiom can also be replaced by axioms of the form:                            We implemented an extra simplification and a deletion rule. Such
                                                                             rules will be denoted using a double line, meaning that the clauses
         Sub(x, xi ) → Sub(x, f (x1 , . . . , xi , . . . , xn )).            in the premise are replaced by the clauses in the conclusion.
                                                                                 The simplification rule is
Using these new axioms will result in fewer inferences during proof
search and a slower growth of the subterm relation, which are                                        f (s) ≈ g(t) ∨ A
important parameters for the provers’ performance.                                                                       Dist-S+ ,
                                                                                                             A
                                                                             where f and g are different constructors. Essentially, it removes
6.    An Extended Calculus                                                   from the clause a literal false in the theory of term algebras.
In this section we describe an alternative way to use superposition             The deletion rule is
theorem provers to reason about term algebras. Instead of including
theory axioms in the initial set of clauses, we extend the calculus                                  f (s) 6≈ g(t) ∨ A
                                                                                                                      Dist-S− ,
with inferences rules. This is similar to the way paramodulation is                                       ∅
used to replace the axiomatization of equality, apart from the fact
that we cannot obtain a calculus that is complete.                           where f and g are different constructors. It deletes a theory tautol-
                                                                             ogy.
6.1   A naive calculus                                                       6.3   The Injectivity Rule
In this section we will consider alternatives and improvements to            There is a simplification rule based on the injectivity axiom (A3).
axiomatizing term algebras. The idea is to add simplification rules          Suppose that f is a constructor of arity n > 0. Then we can use the
specific to term algebras and replace the troublesome acyclicity             simplification rule
axiom by special purpose inference rules.
    The superposition calculus uses term and clause orderings to                              f (s1 . . . sn ) ≈ f (t1 , . . . , tn ) ∨ C
orient equalities, restrict the number of possible inferences, and                                                                            .
simplification. The general rule is that a clause in the search space                                      s1 ≈ t1 ∨ C
can be deleted if it is implied by strictly smaller clauses in the                                             ···
search space.                                                                                              sn ≈ tn ∨ C
    One obvious idea is to add several simplification rules, corre-              One can also note that under some additional restrictions the
sponding to applications of resolution and/or superposition to term          following inference
algebra axioms. For example, a clause f (s) ≈ s ∨ C can be re-
placed by a simpler, yet equivalent, clause C. Likewise, the clause                            f (s1 . . . sn ) 6≈ f (t1 , . . . , tn ) ∨ C
f (s) ≈ f (t) ∨ C is equivalent, by injectivity of the constructors,
to the clause s ≈ t ∨ S. The clause s ≈ t ∨ S is also smaller than                                s1 6≈ t1 ∨ . . . ∨ sn 6≈ tn ∨ C
f (s) ≈ f (t) ∨ C, so it can replace this clause.                            can be considered as a simplification rule too. The restriction is the
    Let us start with examples showing that replacing axioms by              clause ordering condition {s1 6≈ t1 ∨ . . . ∨ sn 6≈ tn } ≺ C.
rules can result in incompleteness even in very simple cases.                   Note that in both rules the premise is logically equivalent to the
    Take for example two ground unit clauses f (a) ≈ b and g(a) ≈            conjunction of the formulas in the conclusion in the theory of term
b, where all symbols apart from b are constructors. This set of              algebras and all formulas in the conclusion are smaller than the
clauses is unsatisfiable in the theory of term algebras. However,            formula in the premise (subject to the ordering condition for the
if we replace the axiom f (x) 6≈ g(y) by a simplification rule, there        second rule).
6.4   The Acyclicity Rule                                                 SMT solvers Z3 and CVC4, and its standardization is under con-
Similar to the distinctness axiom and rules, we can introduce a           sideration.
simplification and a deletion rule based on the acyclicity axiom.             Our input syntax uses declare-datatypes for declaring an
First, we introduce a notion of a constructor subterm as the smallest     abstract data type corresponding to a term algebra sort. This decla-
transitive relation that each of the terms ti is a constructor subterm    ration simultaneously adds the term algebra symbols and the Sub
of f (t1 , . . . , tn ), where f is a constructor and n ≥ i ≥ 1. For      predicate to the problem signature, adds the distinctness, injectiv-
example, if f is a binary constructor, and g is not a constructor, then   ity, domain closure and subterm axioms to the input set of formulas,
all constructor subterms of the term f (f (x, a), g(y)) are f (x, a),     and activates the additional inferences rules from Section 6. Alter-
x, a and g(y). Its subterm y is not a constructor subterm. One can        natively, the user can choose not to activate the inference rules in
easily show that any inequality s 6≈ t, where s is a constructor          our implementation. The inclusion of the Sub predicate and its ax-
subterm of t is false in any extension of term algebras.                  ioms, as presented in Section 5, can also be deactivated.
    The simplification rule for acyclicity is                                 Note that the SMTLIB syntax also provides the not yet stan-
                                                                          dardized command declare-codatatypes to declare types
                             s≈t∨A ,                                      of potentially cyclic or infinite data structures. The theory under-
                                                                          lying the semantics of such types is almost identical to that of fi-
                               A                                          nite term algebras, except that the acyclicity axiom is replaced by
where s is a constructor subterm of t. It deletes from a clause its       a uniqueness rule that asserts that observationally equal terms are
literal false in all term algebras.                                       indeed equal (Reynolds and Blanchette 2015). Therefore our cal-
    The deletion rule is                                                  culus minus the acyclicity axioms/rules is an incomplete but sound
                                                                          inference system for that theory, and users can declare co-algebraic
                             s 6≈ t ∨ A                                   data types in their problems as well. Like acyclicity, the uniqueness
                                           ,
                                                                          principle of co-algebras is not finitely axiomatizable.
                                  ∅
where s is a constructor subterm of t. It deletes a theory tautology.     7.3     Benchmarks
   Further, if we wish to get rid of the subterm relation Sub, we can     We evaluated our implementation on two sets of problems. These
use various rules to treat special cases of acyclicity. If we do this,    problems included all publicly available benchmarks, as mentioned
we will lose completeness even for pure term algebra formulas, but        below.
such a replacement can deal with some formulas more efficiently,
                                                                           • A (parametrized) game theory problem originally described
while still covering a sufficiently large set of problems.
   One example of such a special acyclicity rule is the following:              in (Colmerauer et al. 2000). This problem relies on the term
                                                                                algebra of natural numbers to describe winning and losing po-
                              t≈u∨A                                             sitions of a game. It is possible to encode, for a given posi-
                                                                                tive integer k, a predicate winning k over positions, such that
                              s 6≈ u ∨ A
                                                                                winning k (p) holds iff there exists a winning strategy from the
where s is a constructor subterm of t. Note that this rule is not a             position p in k or fewer moves. The satisfiability of the result-
simplification rule, so we do not delete the premise after applying             ing first-order formula can be checked by term algebra decision
this rule.                                                                      procedures, since it does not use symbols other than those of
                                                                                the term algebra, but it includes 2k alternating universal and
                                                                                existential quantifiers. This heavy use of quantifiers makes it
7.    Experimental Results                                                      an interesting and challenging problem for provers. An exam-
7.1   Implementation                                                            ple of this problem encoded in the SMTLIB syntax is given in
We implemented the subterm relation of Section 5 and simplifi-                  Figure 3.
cation rules of Section 6 in the first-order theorem prover Vam-           • Problems about functional programs, generated by the Isabelle
pire (Kovács and Voronkov 2013). Note that Vampire behaves well                 interactive theorem prover (Nipkow et al. 2002) and translated
on theory problems with quantifiers both at the SMT and first-order             by the Sledgehammer system (Blanchette et al. 2013). The re-
theorem proving competitions, winning respectively 5 divisions in               sulting SMTLIB problems include algebraic and co-algebraic
the SMT-COMP 2016 competition of SMT solvers1 and the quan-                     data types as well as arbitrary types and function symbols, and
tified theory division of the CASC 2016 competition of first-order              also some quantified formulas. Some of these problems are
provers 2 . With our implementation, Vampire becomes the first su-              taken from the Isabelle distribution (Distro) and the Archive
perposition theorem prover able to prove properties of term alge-               of Formal Proofs (AFP), others from a theory about Bird and
bras. Moreover, our experiments described later show that Vampire               Stern–Brocot trees by Peter Gammie and Andreas Lochbihler
outperforms state-of-the-art SMT solvers, such as CVC4 and Z3,                  (G&L). They are representative of the kind of problems corre-
on existing benchmarks.                                                         sponding to program analysis and verification goals. This set
    Our implementation required altogether about 2,500 lines of                 of problems originally appeared in (Reynolds and Blanchette
C++ code. The new version of Vampire, together with our bench-                  2015) and, to the best of our knowledge, represent the set of all
mark suite, is available for download3 .                                        publicly available benchmarks on algebraic data types.

7.2   Input Syntax and Tool Usage                                         7.4     Evaluation
In our work, we used an extended SMTLIB syntax (Barrett et al.            Our experiments were carried out on a cluster on which each node
2016) to describe term constructors. Although not yet part of the         is equipped with two quad core Intel processors running at 2.4 GHz
official SMTLIB standard, this syntax is already supported by the         and 24GiB of memory. To compare our work to other state-of-the-
1 http://smtcomp.sourceforge.net/2016/
                                                                          art systems, we include the results of running the SMT solvers
                                                                          Z3 and CVC4 on the Isabelle problems, as previously reported
2 http://www.cs.miami.edu/~tptp/CASC/J8/
                                                                          in (Reynolds and Blanchette 2015), and also add the results of
3 http://www.cse.chalmers.se/~simrob/tools.html                           running these two solvers on the game theory problem.
(declare-datatypes ()                                                              Vampire     Vampire       Vampire
  ((Nat (z) (s (pred Nat)))))                                                 k                                          CVC4        Z3
                                                                                     (A)        (A+R)       (A+R+S)
                                                                              1      0.01         0.01         0.01       0.01      0.01
(assert                                                                       2      0.01         0.01         0.01       0.01      0.01
  (not                                                                        3      4.98         0.18         0.66         –         –
    (exists                                                                   4      2.21         0.32         0.63         –         –
      ((w1 Nat))                                                              5     35.16        11.17        15.40         –         –
      (and                                                                    6     31.57         8.19        11.33         –         –
        (or                                                                   7       –            –             –          –         –
          (= (s z) (s w1))
          (= (s z) (s (s w1)))                                          Table 1. Time required to prove unsatisfiability of different in-
        )                                                               stances of the game theory problem from (Colmerauer et al. 2000).
        (forall
          ((l0 Nat))
          (=>                                                           Isabelle problems about functional programs. Our results on
            (or                                                         evaluating Vampire on the Isabelle problems are shown in Table 2.
              (= w1 (s l0))                                             The problems were translated by Sledgehammer by selecting some
              (= w1 (s (s l0)))                                         lemmas possibly relevant to a given proof goal in Isabelle and trans-
            )                                                           lating them to SMTLIB along with the negation of the goal. While
            false))))))                                                 the intent of this translation is to produce unsatisfiable first-order
                                                                        problems, this is not the case for all of the problems tested here. A
(check-sat)                                                             few problems are satisfiable and it is likely that many are unprov-
                                                                        able, for example because the lemmas selected by Sledgehammer
Figure 3. An instance of the game theory problem from (Colmer-          are not sufficiently strong to prove the goal. The set of problems
auer et al. 2000), encoded in SMTLIB syntax. The first command          originally included 4170 problems, of which 2869 include at least
declares a term algebra with a constant z and a unary function s;       one algebraic data type and 2825 include at least one co-algebraic
note that the projection function pred must also be named. The          data type, some problems containing both. In the presence of co-
assertion (starting with assert) is a formula corresponding to the      algebraic data types, CVC4 has a special decision procedure which
negation of the predicate winning 1 (s(z)).                             replaces the acyclicity rule by a uniqueness rule. In our implemen-
                                                                        tation, Vampire simply does not add the acyclicity axiom, but the
                                                                        remaining axioms are added as they hold for co-algebraic data types
                                                                        as well. Unlike CVC4, Z3 does not support reasoning about co-
Game theory problems. The times required to solve the game the-         algebraic data types.
ory problem for different values of the parameter k are shown in            In order to test the efficiency of our acyclicity techniques on
Table 1. The first column indicates the time required by Vampire        more examples, we considered problems containing co-algebraic
using the theory axioms (A) described in Section 5, and the sec-        data types: by replacing them with algebraic data types with similar
ond and third columns give the time needed when the simplifica-         constructors, we obtained different problems where the acyclicity
tion rules (R) are also activated in Vampire (Section 6). For this      principle applies. Note that not all co-algebraic data type definitions
particular problem, the acyclicity rule plays no role in the proof,     correspond to a well-founded definition for an algebraic data type:
but in order to assess its impact on performance, the third column      after leaving these out, we obtained 2112 new problems.
shows the times needed to solve the problem when the subterm                Table 2 summarizes our results on this set of benchmarks, using
relation axioms (S) are also included in the input. The fourth and      a single best strategy in Vampire. For each solver, we also show the
fifth columns of Table 1 respectively indicate the times needed by      number of problems solved uniquely only by that solver.
CVC4 and Z3 for solving the corresponding problem. Where no                 We also ran Vampire with a combination of strategies with a
value is given, the prover was unable to solve the problem. Despite     total time limit of 120 seconds. Table 3 shows the total number
belonging to a decidable class, this problem is quite challenging       of solved problems, with details on whether the problems contain
for theorem provers and SMT solvers, which is easily explained by       only algebraic data types, co-algebraic data types, or both. Overall,
the presence of a formula with many quantifier alternations. The        Vampire is able to solve 1785 problems, that is 4,2% more that
SMT solver CVC4 is able to disprove the negated conjecture only         CVC4 and 7,3% more than Z3, which is a significant improvement.
for k = 1, and Z3 can disprove it only for k = 1 or k = 2.              50 problems are uniquely solved by Vampire, as listed in column
SMT solvers can also consider the (non-negated) conjecture and          six Table 3. When compared to Vampire, only 4 problems were
try to satisfy it, but this does not produce better results. In com-    proved by CVC4 alone, while Z3 cannot prove any problem that
parison, our implementation in Vampire can solve the problem for        was not proved by Vampire – see columns seven and eight of
k = 6, that is for formulas with 12 alternated existential and uni-     Table 3. Summarizing, Table 2 shows that Vampire outperforms the
versal quantifiers, in 8.19 seconds. In (Colmerauer et al. 2000), the   best existing solvers so far. The experimental results of Tables 1-
authors are able to solve the problem for k as high as 80, using an     2 provide an evidence that our methods for proving properties of
implementation of the decision procedure presented in (Dao 2000).       algebraic data types outperform methods currently used by SMT
However such a decision procedure would not be able to reason           solvers.
in the presence of uninterpreted symbols, and therefore its usage is
much more restricted. The results of Table 1 confirm that first-order   7.5   Comparison of Option Values
provers can be better suited than SMT solvers for reasoning about       We were also interested in comparing how various proof option
formulas with many quantifiers, despite the various strategies used     values affect the performance of a theorem prover. For the purpose
for quantifier reasoning in SMT solvers (for example, by using E-       of this research, the options that we considered are:
matching (De Moura and Bjørner 2007)). Table 1 also shows that
adding simplification rules as described in Section 6 improves the      1. the Boolean value selecting whether term algebra rules are
behavior of the theorem prover.                                            used;
                                        Total     Vampire     CVC4          Z3         Unique-Vampire     Unique-CVC4         Unique-Z3
                 Data types only        3457        999        956          947              23                0                  0
                Co-data types only      1301        430        415          382              16                2                  0
                      Both              1524        356        341          334              11                2                  0
                     Union              6282       1785       1712         1663              50                4                  0
                               Table 3. Distribution of solved problems according to the data types they feature


                  Prover                 Solved     Unique                                                                off     axioms     rules
                    Z3                    1665        5                                   Total solved                   2030      9086      9602
                  CVC4                    1711       12                                   Solved by only this value       50        70        566
           Vampire (Best strategy)        1720       31
                                                                                  Table 4. Comparison of proof option values for acyclicity in Vam-
Table 2. Number of problems solved among the 6282 Isabelle                        pire.
problems translated by SledgeHammer.


2. the value selecting how acyclicity is treated (axioms, rule, or                8.     Related Work
   none, that is, no acyclicity axioms or rules).                                 The problem of reasoning over term algebras first appears in the
                                                                                  restricted form of syntactic unification, mentioned in (Herbrand
   Making such a comparison is hard, since there is no obvious                    1930). The algorithm for syntactic unification was later described
methodology for doing so, especially considering that Vampire has                 in (Robinson 1965), and later refined into quasi-linear (Baxter
64 options commonly used in experiments. The majority of these                    1976; Huet 1976; Martelli and Montanari 1982) and linear algo-
parameters are boolean, some are finitely-valued, some integer-                   rithms (Paterson and Wegman 1976).
valued and some range over other infinite domains. The method                         The full-first order theory of term algebras over a finite sig-
we used was based on the following ideas. Suppose we want to                      nature was first studied in (Mal’cev 1962), where its decidability
compare values for an option π. Then:                                             was proved by quantifier elimination. Other quantifier elimination
1. we use a set of problems obtained by discarding problems that                  procedures appeared in (Comon 1988; Maher 1988; Hodges 1993;
   are too easy or currently unsolvable;                                          Rybina and Voronkov 2001). (Ferrante and Rackoff 1979) proved
                                                                                  a result implying that the first-order theory of term algebras is non-
2. we repeatedly select a random problem P in this set, a random                  elementary. There is a large body of research on decidability of var-
   strategy S and run P on variants of S obtained by choosing all                 ious extensions of term algebras, which we do not describe here.
   possible values for π using the same time limit.                                   In this paper we do not prove decidability of new theories. How-
We discovered that the results for the term algebra rules are incon-              ever, we present a new superposition-based decision procedure for
clusive (turning them on or off makes little effect on the results)               first-order theories of term algebras using a finitely axiomatizable
and will present the results for the acyclicity option.                           theory.
   Our selected set of problems consisted of 262 term algebra                         Probably the first implementation of a decision procedure for
problems. We made 90,000 runs for each value (off, theory axioms,                 term algebras is described in (Colmerauer et al. 2000). The theory
and simplification rules), that is, 270,000 tests all together, with the          of finite or infinite trees is also studied in (Dao 2000) and a practical
time limit of 30 seconds. While interpreting the results, it is worth             decision procedure is given based on rewriting.
mentioning the following.                                                             Due to recent applications of program analysis, there is now a
                                                                                  growing interest in the automated reasoning community for practi-
1. When neither acyclicity rules nor acyclicity axioms are used,                  cal implementation of term algebras and their combinations with
   problems whose proof rely on acyclicity become unsolvable.                     other theories. A decision procedure for algebraic data types is
   On the other hand, for other problems, this setting results in a               given in (Barrett et al. 2007) and later extended to a decision
   smaller search space.                                                          procedure for co-algebraic data types in (Reynolds and Blanchette
                                                                                  2015). These decision procedures exploit SMT-style reasoning and
2. When acyclicity simplification rules are used, the resulting cal-
                                                                                  are supported by CVC4. Z3 also supports proving properties about
   culus is incomplete even for pure term algebra problems, but the
                                                                                  algebraic data types (Bjorner et al. 2013). Unlike these techniques,
   subterm relation is not used, which generally means that fewer
                                                                                  our work targets the full first-order theory of term algebras, with
   clauses should be generated.
                                                                                  arbitrary use of quantifiers. Our proof search procedure is based on
    The results of these experiments are shown in Table 4. We show                the superposition calculus and allows one to prove properties with
the total number of successful runs (out of 90,000) and the number                both theories and quantifiers.
of runs where only one value for this option solved the problem.
Probably the most interesting observation is that using acyclicity
simplification rules (Section 6) instead of theory axioms (Section 5)             9.     Conclusion
results in many more problems solved. This gives us an evidence                   We presented two different ways to reason in the presence of the
that the axiomatization based on the subterm relation results in                  theory of finite term algebras with a superposition-based first-order
much larger search spaces. This also means that the value resulting               theorem prover. Our first approach is based on a finitely axiomati-
in an incomplete strategy in this case generally behaves better.                  zable conservative extension of the theory and can be implemented
    One should also note the 50 problems solved only when turning                 in any first-order theorem prover. The second technique extends the
acyclicity off. This means that even the light-weight rule-based                  first with the addition of extra inference and simplification rules
treatment of acyclicity sometimes results in a large overhead.                    having two aims:
Moreover, out of these 50 problems 10 were solved in less than
1 second.                                                                         1. simplifying more clauses;
2. replacing expensive subterm-based reasoning about acyclicity               L. D. Baxter. The complexity of unification. PhD thesis, University of
   by light-weight inference rules (though incomplete even with-                 Waterloo Waterloo, Ontario, 1976.
   out uninterpreted functions).                                              N. Bjorner, K. McMillan, and A. Rybalchenko. Higher-order program
                                                                                 verification as satisfiability modulo theories with algebraic data-types.
While not as efficient as specialized decision procedures for this               arXiv preprint arXiv:1306.5264, 2013.
theory, both our techniques allow us to reason about problems that            J. C. Blanchette, S. Böhme, and L. C. Paulson. Extending Sledgehammer
includes the theory of finite terms algebras and other predicate or              with SMT solvers. Automated Deduction–Cade-23, 6803:116–130,
function symbols. We evaluated our work on game theory con-                      2013.
straints and properties of functional program manipulating alge-              K. Claessen, M. Johansson, D. Rosén, and N. Smallbone. Automating
braic data types.                                                                inductive proofs using theory exploration. In Automated Deduction–
    The next natural development would be to extend our approach                 CADE-24, volume 7898 of LNCS, pages 392–406. Springer, 2013.
to the theories of rational (finite but possibly cyclic) and infinite         K. L. Clark. Negation as failure. In Logic and data bases, pages 293–322.
term algebras. The notion of co-algebras is also closely related to              Springer, 1978.
possibly infinite terms, with the addition of a uniqueness principle
                                                                              A. Colmerauer et al. Expressiveness of full first order constraints in
for cyclic terms. A decision procedure for this theory was included              the algebra of finite or infinite trees. In Principles and Practice of
in the SMT solver CVC4 to decide problems involving co-algebraic                 Constraint Programming–CP 2000, volume 1894 of LNCS, pages 172–
data types (Reynolds and Blanchette 2015). Co-algebras are also                  186. Springer, 2000.
best suited to express the semantics of processes and structures              H. Comon. Unification et disunification: Théorie et applications. PhD
involving a notion of state. Unlike term algebras, co-algebras have              thesis, Institut National Polytechnique de Grenoble-INPG, 1988.
been studied almost exclusively from the point of view of category
                                                                              B. Courcelle. Fundamental properties of infinite trees. Theoretical
theory, rather than that of first-order logic, so that many theoretical          computer science, 25(2):95–169, 1983.
and practical applications remain to be explored there.
    An even more interesting avenue to exploit is inductive reason-           T. B. H. Dao. Résolution de contraintes du premier ordre dans la théorie
                                                                                 des arbres finis ou infinis. PhD thesis, Université Aix-Marseille 2, 2000.
ing about algebraic data types in first-order theorem proving, also
based on extensions of the superposition calculus.                            L. De Moura and N. Bjørner. Efficient e-matching for smt solvers. In
    The work presented here should be a useful development for the               International Conference on Automated Deduction, volume 4603 of
verification of functional programs. For example it would benefit                LNCS, pages 183–198. Springer, 2007.
the tool HALO (Vytiniotis et al. 2013), which expresses the deno-             L. M. de Moura and N. Bjørner. Z3: An Efficient SMT Solver. In TACAS,
tational semantics of Haskell programs in first-order logic, before              volume 4963 of LNCS, pages 337–340. Springer, 2008.
using automated theorem provers to verify some of their proper-               J. Ferrante and C. W. Rackoff. The computational complexity of logical
ties. Our work not only makes the translation easier but also modi-               theories, volume 718 of Lecture Notes in Mathematics. Springer-Verlag,
fies the prover to make it more efficient on the generated problems.              1979.
This also applies to other tools that already use first-order theorem         J. A. Goguen, J. W. Thatcher, E. G. Wagner, and J. B. Wright. Initial algebra
provers to discharge their proof obligations, such as inductive theo-             semantics and continuous algebras. Journal of the ACM (JACM), 24(1):
rem provers, e.g. HipSpec (Claessen et al. 2013) and automated rea-               68–95, 1977.
soning tools for higher-order logic, e.g. Sledgehammer (Blanchette            J. Herbrand. Recherches sur la théorie de la démonstration. PhD thesis,
et al. 2013).                                                                    Université de Paris, 1930.
    More generally, our work makes an important step towards clos-            W. Hodges. Model Theory. Cambridge University Press, 1993.
ing the gap between SMT solvers and first-order theorem provers.              G. Huet. Résolution d’équations dans des langages d’ordre 1, 2... PhD
The former are traditionally used for problems involving theories,               thesis, Université Paris VII, 1976.
while the latter are better at dealing with quantifiers. Problems that
                                                                              K. Korovin and A. Voronkov. Integrating linear arithmetic into superpo-
include both quantifiers and theories are very common in practi-                 sition calculus. In Computer Science Logic, volume 4646 of Lecture
cal applications and represent a big challenge due to their intrinsic            Notes in Computer Science, pages 223–237. Srpinger, 2007.
complexity, both in theory and in practice. Our results show that
                                                                              L. Kovács and A. Voronkov. First-Order Theorem Proving and Vampire. In
first-order theorem provers can perform efficient reasoning in the               Proceedings of CAV, volume 8044 of LNCS, pages 1–35, 2013.
presence of theories, solving many problems previously unsolvable
by other tools.                                                               M. J. Maher. Complete axiomatizations of the algebras of finite, rational
                                                                                and infinite trees. In Proceedings of the Third Annual Symposium
                                                                                onLogic in Computer Science, pages 348–357. IEEE Computer Society,
Acknowledgments                                                                 1988.
We acknowledge funding from the ERC Starting Grant 2014 SYM-                  A. I. Mal’cev. Axiomatizable classes of locally free algebras of certain
                                                                                 types. Sibirsk. Mat. Zh, 3:729–743, 1962.
CAR 639270, the Wallenberg Academy Fellowship 2014 TheP-
roSE, the Swedish VR grant GenPro D0497701, the Austrian FWF                  A. Martelli and U. Montanari. An efficient unification algorithm. ACM
research project RiSE S11409-N23, and the EPSRC grant ReVeS:                     Transactions on Programming Languages and Systems (TOPLAS), 4(2):
                                                                                 258–282, 1982.
Reasoning for Verification and Security.
                                                                              R. Nieuwenhuis and A. Rubio. Paramodulation-Based Theorem Proving.
                                                                                 In A. Robinson and A. Voronkov, editors, Handbook of Automated
References                                                                       Reasoning, volume I, chapter 7, pages 371–443. Elsevier Science, 2001.
C. Barrett, I. Shikanian, and C. Tinelli. An abstract decision procedure      T. Nipkow, L. C. Paulson, and M. Wenzel. Isabelle/HOL - A Proof Assistant
   for a theory of inductive data types. Journal on Satisfiability, Boolean      for Higher-Order Logic, volume 2283 of LNCS. Springer, 2002.
   Modeling and Computation, 3:21–46, 2007.                                   M. S. Paterson and M. N. Wegman. Linear unification. In Proceedings
C. Barrett, C. Conway, M. Deters, L. Hadarean, D. Jovanovic, T. King,           of the eighth annual ACM symposium on Theory of computing, pages
   A. Reynolds, and C. Tinelli. CVC4. In CAV, volume 6806 of LNCS.              181–186. ACM, 1976.
   Springer, 2011.                                                            A. Reynolds and J. C. Blanchette. A decision procedure for (co)datatypes
C. Barrett, P. Fontaine, and C. Tinelli. The Satisfiability Modulo Theories      in SMT solvers. In Automated Deduction–CADE-25, volume 9195 of
   Library (SMT-LIB). www.SMT-LIB.org, 2016.                                     LNCS, pages 197–213. Springer, 2015.
J. A. Robinson. A machine-oriented logic based on the resolution principle.   S. G. Vorobyov and A. Voronkov. Complexity of nonrecursive logic
    Journal of the ACM (JACM), 12(1):23–41, 1965.                                programs with complex values. In Proceedings of the seventeenth
T. Rybina and A. Voronkov. A decision procedure for term algebras with           ACM SIGACT-SIGMOD-SIGART symposium on Principles of database
   queues. ACM Transactions on Computational Logic, 2(2):155–181,                systems, pages 244–253. ACM Press, 1998.
   2001. doi: 10.1145/371316.371494.                                          D. Vytiniotis, S. Peyton Jones, K. Claessen, and D. Rosén. HALO:
S. Schulz. E - a brainiac theorem prover. AI Communications, 15(2-3):            Haskell to logic through denotational semantics. In Proceedings of
   111–126, 2002.                                                                the 40th Annual ACM SIGPLAN-SIGACT Symposium on Principles of
                                                                                 Programming Languages, POPL ’13, pages 431–442. ACM, 2013.
K. Venkataraman. Decidability of the purely existential fragment of the
   theory of term algebras. Journal of the ACM (JACM), 34(2):492–510,
   1987.
