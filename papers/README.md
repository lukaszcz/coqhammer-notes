# Reference papers (text extracts)

Plain-text extracts of the papers referenced in `../extraction.md`,
`../monomorphisation.md`, `../type_guards.md` and `../dependent_types.md`.
Math notation is approximate; consult the original PDFs for formulas.

## Papers referenced in `../extraction.md`

Produced with pypdf (2026-07-05). Page boundaries are marked with
`===== PAGE n =====` (PDF page numbers, which are offset from the printed
page numbers in the thesis).

| File | Source |
|------|--------|
| `letouzey-phd-thesis-2004-french.txt` | P. Letouzey, *Programmation fonctionnelle certifiée — L'extraction de programmes dans l'assistant Coq*, PhD thesis, Université Paris-Sud, 2004. https://theses.hal.science/tel-00150912/document (French; the English PDF on the author's page uses Type-3 fonts and does not yield extractable text) |
| `letouzey-new-extraction-types2002.txt` | P. Letouzey, *A New Extraction for Coq*, TYPES 2002, LNCS 2646. https://www.irif.fr/~letouzey/download/extraction2002.pdf |
| `letouzey-extraction-overview-cie2008.txt` | P. Letouzey, *Extraction in Coq: an Overview*, CiE 2008, LNCS 5028. https://www.irif.fr/~letouzey/download/letouzey_extr_cie08.pdf |
| `czajka-kaliszyk-hammer-for-coq-jar2018.txt` | Ł. Czajka, C. Kaliszyk, *Hammer for Coq: Automation for Dependent Type Theory*, J. Autom. Reasoning 61:423–453, 2018. https://link.springer.com/content/pdf/10.1007/s10817-018-9458-4.pdf |

## Papers referenced in `../monomorphisation.md`

Produced with pdftotext (2026-07-05), no page markers. The JAR 2018 and
Letouzey papers above are shared references of both notes.

| File | Source |
|------|--------|
| `czajka-2016-shallow-embedding-pts-fol-types.txt` | Ł. Czajka, *A Shallow Embedding of Pure Type Systems into First-Order Logic*, TYPES 2016 post-proceedings, LIPIcs 97, 9:1–9:39. https://drops.dagstuhl.de/storage/00lipics/lipics-vol097-types2016/LIPIcs.TYPES.2016.9/LIPIcs.TYPES.2016.9.pdf |
| `czajka-kaliszyk-2016-goal-translation-hatt.txt` | Ł. Czajka, C. Kaliszyk, *Goal Translation for a Hammer for Coq (Extended Abstract)*, HaTT 2016, EPTCS 210, pp. 13–20. http://eptcs.web.cse.unsw.edu.au/paper.cgi?HaTT2016.4.pdf |
| `blanchette-bohme-popescu-smallbone-2016-encoding-types-lmcs.txt` | J. C. Blanchette, S. Böhme, A. Popescu, N. Smallbone, *Encoding Monomorphic and Polymorphic Types*, LMCS 12(4:13), 2016. https://arxiv.org/abs/1609.08916 |
| `claessen-lillistrom-smallbone-2011-sort-it-out-monotonicity-cade.txt` | K. Claessen, A. Lillieström, N. Smallbone, *Sort It Out with Monotonicity*, CADE-23, LNAI 6803, pp. 207–221, 2011. https://smallbone.se/papers/sort-it-out-with-monotonicity.pdf |
| `bobot-paskevich-2011-polymorphic-types-many-sorted-frocos-extended.txt` | F. Bobot, A. Paskevich, *Expressing Polymorphic Types in a Many-Sorted Language*, FroCoS 2011; **extended INRIA report** (37 pp.). https://inria.hal.science/inria-00591414/ |
| `leino-rummer-2010-polymorphic-ivl-boogie2-tacas.txt` | K. R. M. Leino, P. Rümmer, *A Polymorphic Intermediate Verification Language: Design and Logical Encoding*, TACAS 2010, LNCS 6015. http://www.philipp.ruemmer.org/publications/boogie-type-encoding.pdf |
| `meng-paulson-2008-translating-ho-clauses-jar.txt` | J. Meng, L. C. Paulson, *Translating Higher-Order Clauses to First-Order Clauses*, JAR 40(1):35–60, 2008. https://www.cl.cam.ac.uk/~lp15/papers/Automation/translations-jar.pdf |
| `desharnais-vukmirovic-blanchette-wenzel-2022-seventeen-provers-itp.txt` | M. Desharnais, P. Vukmirović, J. C. Blanchette, M. Wenzel, *Seventeen Provers Under the Hammer*, ITP 2022, LIPIcs 237. https://matryoshka-project.github.io/pubs/seventeen.pdf |
| `bhayat-reger-2020-polymorphic-vampire-ijcar.txt` | A. Bhayat, G. Reger, *A Polymorphic Vampire (Short Paper)*, IJCAR 2020, LNCS 12167. https://pmc.ncbi.nlm.nih.gov/articles/PMC7324017/ |
| `bartek-et-al-2025-vampire-diary-cav.txt` | F. Bártek et al., *The Vampire Diary*, CAV 2025. https://arxiv.org/abs/2506.03030 (v3) |
| `qian-clune-barrett-avigad-2025-lean-auto-cav.txt` | Y. Qian, J. Clune, C. Barrett, J. Avigad, *Lean-auto: An Interface between Lean 4 and Automated Theorem Provers*, CAV 2025. https://arxiv.org/abs/2505.14929 |
| `zhu-clune-avigad-jiang-welleck-2025-leanhammer-premise-selection-iclr.txt` | T. Zhu, J. Clune, J. Avigad, A. Q. Jiang, S. Welleck, *Premise Selection for a Lean Hammer* (ICLR 2026 version). https://arxiv.org/abs/2506.07477 |
| `blanchette-sledgehammer-users-guide.txt` | J. C. Blanchette, *Hammering Away: A User's Guide to Sledgehammer* (Isabelle documentation; `max_mono_iters`, `max_new_mono_instances` defaults). https://isabelle.in.tum.de/doc/sledgehammer.pdf |

## Papers referenced in `../type_guards.md`

Produced with pdftotext (2026-07-05), no page markers. Shared references
already listed above: JAR 2018, HaTT 2016, the PTS embedding (LIPIcs), LMCS
2016, Sort It Out (CADE-23), Bobot–Paskevich (extended), Leino–Rümmer,
Meng–Paulson, the Letouzey items, the Sledgehammer guide.

| File | Source |
|------|--------|
| `blanchette-kaliszyk-paulson-urban-2016-hammering-towards-qed-jfr.txt` | J. Blanchette, C. Kaliszyk, L. Paulson, J. Urban, *Hammering towards QED*, J. Formalized Reasoning 9(1):101–148, 2016. https://jfr.unibo.it/article/view/4593 |
| `blanchette-bohme-smallbone-2012-monotonicity-draft.txt` | J. C. Blanchette, S. Böhme, N. Smallbone, *Monotonicity or How to Encode Polymorphic Types Safely and Efficiently* (draft, 2012). https://www21.in.tum.de/~blanchet/mono-trans.pdf |
| `urban-2004-dissertation-mptp-mizar.txt` | J. Urban, *Exploring and Combining Deductive and Inductive Reasoning in Large Libraries of Formalized Mathematics*, PhD dissertation, Charles University, 2004 (contains the MPTP JAR 2004 / MKM 2003 papers — Mizar type relativization, `set`-guard omission). http://people.ciirc.cvut.cz/~urbanjo3/dissall.pdf |
| `kaliszyk-urban-2013-mizar40-for-mizar40.txt` | C. Kaliszyk, J. Urban, *MizAR 40 for Mizar 40*, JAR 55(3), 2015. https://arxiv.org/abs/1310.2805 |
| `bobot-conchon-contejean-lescuyer-2008-polymorphism-in-smt.txt` | F. Bobot, S. Conchon, E. Contejean, S. Lescuyer, *Implementing Polymorphism in SMT solvers*, SMT 2008 (Alt-Ergo's native polymorphism). |
| `abel-scherer-2012-on-irrelevance-lmcs.txt` | A. Abel, G. Scherer, *On Irrelevance and Algorithmic Equality in Predicative Type Theory*, LMCS 8(1:29), 2012 (erasure vs internal irrelevance caveats). https://arxiv.org/abs/1203.4716 |
| `rocq-manual/*.rst` | Rocq reference manual sources (`rocq-prover/rocq`, `doc/sphinx/language/`): `cic.rst` (typing rules, subtyping/cumulativity), `inductive.rst` (W-Ind, match, Fix), `sorts.rst`, `conversion.rst`, `sprop.rst`. Already textual; rule names match https://rocq-prover.org/doc/master/refman/language/cic.html |
| `why3-src/*.ml` | Why3 `src/transform/` sources (gitlab.inria.fr/why3/why3): `why3_encoding_guards.ml` is the production featherweight-guards (`g??`) implementation cited in `../type_guards.md` §3.4; also `encoding_tags`, `discriminate`, `libencoding`, `twin`, `select`. |

## Papers referenced in `../dependent_types.md`

Produced with pdftotext (2026-07-05), no page markers. Shared references
already listed above: JAR 2018, the PTS embedding (LIPIcs), the three
Letouzey items (thesis, TYPES 2002, CiE 2008), LMCS 2016, Meng–Paulson,
Lean-auto.

| File | Source |
|------|--------|
| `paulin-mohring-1989-extracting-fw-programs-popl.txt` | C. Paulin-Mohring, *Extracting Fω's Programs from Proofs in the Calculus of Constructions*, POPL 1989, pp. 89–104. OCR'd scan via Wayback Machine: http://web.archive.org/web/20240708161341/https://dl.acm.org/doi/pdf/10.1145/75277.75285 (OCR quality is imperfect, headers garbled; body text usable) |
| `gilbert-cockx-sozeau-tabareau-2019-sprop-popl.txt` | G. Gilbert, J. Cockx, M. Sozeau, N. Tabareau, *Definitional Proof-Irrelevance without K*, PACMPL 3(POPL):3, 2019. https://jesper.sikanda.be/files/definitional-proof-irrelevance-without-K.pdf |
| `sozeau-mangin-2019-equations-reloaded-icfp.txt` | M. Sozeau, C. Mangin, *Equations Reloaded: High-Level Dependently-Typed Functional Programming and Proving in Coq*, PACMPL 3(ICFP):86, 2019. https://sozeau.gitlabpages.inria.fr/www/research/publications/Equations_Reloaded-ICFP19.pdf |
| `wiedijk-2007-mizar-soft-type-system-tphols.txt` | F. Wiedijk, *Mizar's Soft Type System*, TPHOLs 2007, LNCS 4732, pp. 383–399. https://www.cs.ru.nl/~freek/mizar/miztype.pdf |
| `sinkarovs-rawson-2026-when-agda-met-vampire.txt` | A. Šinkarovs, M. Rawson, *When Agda met Vampire*, arXiv:2602.18844, 2026. https://arxiv.org/pdf/2602.18844 |
| `tammet-smith-1996-optimized-encodings-type-theory-fol.txt` | T. Tammet, J. M. Smith, *Optimized Encodings of Fragments of Type Theory in First Order Logic*, TYPES '95 post-proceedings, LNCS 1158, pp. 265–287, 1996. Author's self-archived preprint (`autolncs.ps`, 23 pp.) recovered from the Wayback Machine capture of Tammet's Chalmers page: http://web.archive.org/web/20010603224337/http://www.cs.chalmers.se/~tammet/autolncs.ps (converted ps→pdf→txt with Ghostscript 10.01.2). Note: this is the conference version; the JLC 8(6), 1998 journal version (pp. 713–744) extends it and remains paywalled. |

**Not available:** J.-F. Couchot, S. Lescuyer, *Handling Polymorphism in
Automated Deduction* (CADE-21, 2007) — no open-access copy exists (checked
publisher, author pages, OpenAlex/Semantic Scholar, Wayback Machine; also
traced CiteSeerX record 10.1.1.100.6196 to its crawl source
`www.lri.fr/~couchot/IMG/pdf_CADE_couchot_lescuyer.pdf`, dead since ~2015 and
never captured with status 200; Couchot's current FEMTO-ST page does not list
it). The discussions in `../monomorphisation.md` and `../type_guards.md` rely
on its treatment in the Blanchette et al. and Bobot–Paskevich papers above.
Last resort: email the authors.

**Note on Tammet–Smith:** only the extended journal version (JLC 8(6), 1998)
remains unavailable (OUP paywall); the TYPES '95/LNCS 1158 conference version
is in the collection (see the `../dependent_types.md` table above), recovered
via the Wayback Machine from the author's self-archived preprint.

Quick orientation (line numbers may drift; grep for section titles):

- Thesis: `E` function — Définition 9 (§2.2, PDF p. 58); simulation predicates
  `⟦·⟧` (§2.4.2–2.4.3, PDF pp. 73–76); `div` realizability example (§2.4.4);
  empty inductives / singleton elimination / `□`-arguments (§2.6, PDF pp.
  90–94); typing and `Ê` (§3.3.5, PDF p. 120); logical-argument and
  inductive-type optimizations (§4.3.1–4.3.2, PDF pp. 141–145).
- JAR 2018: translation functions F/G/C incl. the case-expression axiom (§5.2,
  PDF pp. 12–14); guard soundness discussion (§5.6, PDF p. 17); limitations and
  the suggestion to factorize through Letouzey's intermediate representation
  (§9, PDF pp. 26–27).
- PTS embedding (LIPIcs 2016): translation rules and axiom sets Δ (Defs.
  35–50); soundness Thm. 75/Cor. 77; incompleteness Example 51; §6 remarks on
  guard-free `Δ_Φ`, dropping `𝔸_Γ`, and adapting monotonicity inference.
- LMCS 2016: encodings g/t (§3), monotonicity calculus and naked variables
  (§5.1–5.2), lightweight/featherweight g?/g??/t?/t?? (§5.3–5.5), heuristic
  monomorphisation definition (§5.6), Sledgehammer implementation with
  K/Δ bounds and infinity detection (§7.1–7.4), evaluation (§8).
- Sort It Out (CADE 2011): monotone erasure Thm. 1; simple linear calculus vs
  NP-complete SAT calculus (§3); per-sort predicate/function translation (§4).
- Bobot–Paskevich (extended report): undecidability of complete
  monomorphisation Thm. 1 (§2); Dis/Tw/Dec-Exp-Grd pipeline (§4–6);
  evaluation incl. Dis+Grd vs Grd (§8).
- Seventeen Provers (ITP 2022): encoding comparison tables (§5, Tables 8–9):
  native TF1/TH1 vs monomorphised untyped vs TF0.
- Lean-auto (CAV 2025): constant instances and dependent arguments (§4);
  saturation Algorithm 1 with global `maxInsts` cap; QMono filter; λ→*
  abstraction and universe lifting (§5).
- Hammering towards QED (JFR 2016): §3 — history of Sledgehammer's unsound →
  monotonicity-based encoding migration; the three costs of unsound light
  encodings (exhaustion-rule filtering, spurious proofs, premise selection
  learning inconsistencies); guarded `nil/cons/hd/tl` worked example.
- Urban dissertation: Mizar type-predicate translation and relativization,
  conditional cluster axioms (`cardinal(X) ⇒ Ordinal-like(X)`), the `set`
  top-type guard omission, axiom-set minimization (570 → 73).
- Rocq manual `cic.rst`: the four Prod rules, Conv, subtyping rules 1–6 (rule 5
  = convertible domains, the argument-position rigidity fact used for typing
  inversion in `../type_guards.md` §2.2).
- `why3-src/why3_encoding_guards.ml`: the deployed `g??` guard-skip condition
  (`is_protected_vs || (polar && sign=(q=Tforall) && (not naked || infinite))`).
- Paulin-Mohring (POPL 1989): the realizability relation defined structurally on
  types (informative ∀ → guarded ∀, logical premises → implications, Σ/subset
  content → conjunction with the predicate) — the model for `../dependent_types.md`
  §5.2's shallow spec extraction; informative vs non-informative propositions.
- SProp (POPL 2019): §on singleton elimination and why irrelevant `eq` does not
  yield K definitionally — the soundness boundary for `eq`-match erasure discussed
  in `../dependent_types.md` §6.
- Equations Reloaded (ICFP 2019): derived equations, graph and functional
  elimination for dependent pattern matching — the alternative spec source
  dismissed as a general mechanism in `../dependent_types.md` §5.6.
- Wiedijk (TPHOLs 2007): Mizar adjectives = types-as-predicates; subset types as
  adjectives on a mother type — structurally the `T(w,A) ∧ P w` guard expansion.
- When Agda met Vampire (2026): the equational-Horn shared fragment and two-way
  translation; supports the "equations + Horn specs are the ATP currency" thesis.
- Tammet–Smith (1996): sound and complete FOL translations of fragments of
  Martin-Löf monomorphic type theory, optimised per fragment; the historical
  precedent for type-guard encodings of dependent products cited in
  `../dependent_types.md` §3. (Ligatures are lost in the text extract: "rst" =
  "first", etc.)
