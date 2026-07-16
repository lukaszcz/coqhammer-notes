# Archived papers for `notes/indexed_families.md`

Each paper is stored as the original PDF plus a `pdftotext -layout` conversion
(`.txt`) for agent-readable access. Formulas in the `.txt` files may be
garbled where PDFs use symbol fonts; consult the PDF for exact statements.

| File | Citation |
|---|---|
| `mcbride-1999-thesis-dependently-typed-functional-programs` | C. McBride, *Dependently Typed Functional Programs and their Proofs*, PhD thesis, U. Edinburgh, 1999. Fording / elimination with equational constraints: §3.5. |
| `goguen-mcbride-mckinna-2006-eliminating-dependent-pattern-matching` | H. Goguen, C. McBride, J. McKinna, "Eliminating Dependent Pattern Matching", *Algebra, Meaning and Computation* (Goguen Festschrift), LNCS 4060, 2006. |
| `cockx-devriese-piessens-2014-pattern-matching-without-k` | J. Cockx, D. Devriese, F. Piessens, "Pattern Matching Without K", ICFP 2014. |
| `cockx-devriese-2018-proof-relevant-unification` | J. Cockx, D. Devriese, "Proof-relevant unification: Dependent pattern matching with only the axioms of your type theory", JFP 28, 2018. |
| `brady-mcbride-mckinna-2003-inductive-families-need-not-store-indices` | E. Brady, C. McBride, J. McKinna, "Inductive Families Need Not Store Their Indices", TYPES 2003, LNCS 3085. **PDF only** — the available PDF's fonts lack ToUnicode maps, so no readable text conversion exists; see the research reports for a digest. |
| `letouzey-2002-a-new-extraction-for-coq` | P. Letouzey, "A New Extraction for Coq", TYPES 2002, LNCS 2646. |
| `sozeau-mangin-2019-equations-reloaded` | M. Sozeau, C. Mangin, "Equations Reloaded", ICFP 2019 (PACMPL 3). |
| `gilbert-cockx-sozeau-tabareau-2019-definitional-proof-irrelevance-without-k` | G. Gilbert, J. Cockx, M. Sozeau, N. Tabareau, "Definitional Proof-Irrelevance without K", POPL 2019 (PACMPL 3). |
| `monin-2010-proof-trick-small-inversions` | J.-F. Monin, "Proof Trick: Small Inversions", 2010. (Substitute for Monin & Shi, "Handcrafted Inversions Made Operational on Operational Semantics", ITP 2013, LNCS 7998 — no open PDF found.) |
| `swamy-etal-2016-fstar-dependent-types-multi-monadic-effects` | N. Swamy et al., "Dependent Types and Multi-Monadic Effects in F*", POPL 2016. |
| `meng-paulson-2008-translating-higher-order-clauses` | J. Meng, L. C. Paulson, "Translating Higher-Order Clauses to First-Order Clauses", JAR 40, 2008. |
| `blanchette-boehme-paulson-2013-extending-sledgehammer-with-smt` | J. C. Blanchette, S. Böhme, L. C. Paulson, "Extending Sledgehammer with SMT Solvers", JAR 51, 2013. |
| `atkey-2018-syntax-semantics-quantitative-type-theory` | R. Atkey, "Syntax and Semantics of Quantitative Type Theory", LICS 2018. |
| `vazou-etal-2014-refinement-types-for-haskell` | N. Vazou et al., "Refinement Types for Haskell", ICFP 2014. |

Additional texts fetched by the research agents (text-only, no PDF kept):

| File | Citation |
|---|---|
| `mcbride-2014-how-to-keep-your-neighbours-in-order` | C. McBride, "How to Keep Your Neighbours in Order", ICFP 2014. Origin of the "green slime" term (§4). |
| `zhang-2023-two-tricks-to-trivialize-higher-indexed-families` | T. Zhang, "Two Tricks to Trivialize Higher-Indexed Families", arXiv:2309.14187. Datatype-level fording, general `c_Ford` shape. |
| `kovacs-robillard-voronkov-2017-coming-to-terms-with-quantified-reasoning` | L. Kovács, S. Robillard, A. Voronkov, "Coming to Terms with Quantified Reasoning", POPL 2017. FO theory of term algebras, acyclicity schema. |
| `monin-shi-2013-handcrafted-inversions-itp13-slides` | Monin & Shi ITP 2013 talk slides (paper itself paywalled). |
| `monin-2022-small-inversions-for-smaller-inversions` | J.-F. Monin, TYPES 2022 abstract. |
| `brady-2021-idris2-quantitative-type-theory-in-practice` | E. Brady, "Idris 2: Quantitative Type Theory in Practice", ECOOP 2021. |
| `lee-werner-2011-proof-irrelevant-model-of-cc` | G. Lee, B. Werner, "Proof-irrelevant model of CC with predicative induction and judgmental equality", LMCS 7(4:05), 2011. |
| `werner-2008-on-the-strength-of-proof-irrelevant-type-theories` | B. Werner, "On the Strength of Proof-Irrelevant Type Theories", LMCS 4(3:13), 2008. |
| `sozeau-etal-2020-coq-coq-correct` | M. Sozeau, S. Boulier, Y. Forster, N. Tabareau, T. Winterhalter, "Coq Coq Correct! Verification of Type Checking and Erasure for Coq, in Coq", POPL 2020 (PACMPL 4). |
| `letouzey-2008-extraction-in-coq-an-overview` | P. Letouzey, "Extraction in Coq: an Overview", CiE 2008, LNCS 5028. |
| `rocq-manual-inductive.rst` | Rocq reference manual source, *Theory of inductive definitions* — official empty/singleton elimination criterion. |
| `metacoq-Extract.v`, `metacoq-PCUICElimination.v` | MetaCoq sources: `isErasable` and the `Subsingleton` (formerly `Informative`) elimination condition. |

Referenced but not archived (bot-blocked at ACM/HAL/Springer at time of
writing; cite from the research reports):

- M. Sozeau, Y. Forster, M. Lennon-Bertrand, J. B. Nielsen, N. Tabareau,
  T. Winterhalter, "Correct and Complete Type Checking and Certified Erasure
  for Coq, in Coq", JACM 72(1), 2025. <https://inria.hal.science/hal-04077552>
- J.-C. Filliâtre, A. Paskevich, "Why3 — Where Programs Meet Provers",
  ESOP 2013, LNCS 7792. <https://inria.hal.science/hal-00789533>
- J.-F. Monin, X. Shi, "Handcrafted Inversions Made Operational on
  Operational Semantics", ITP 2013, LNCS 7998.
