# Referee Report

**Manuscript:** *Fording: A Sound Shallow Translation of Indexed Inductive Families into First-Order Logic*
**Review round:** 1
**Date:** 2026-07-17
**Reviewer expertise:** proof automation for dependent type theory, semantics of CIC, first-order encodings (expert)

**Recommendation: Major revision.**

The mathematics is essentially sound — I verified the central construction and every main proof in detail and found no error that threatens Theorems 7.6–7.8 (env-validity, soundness, consistency) or the design-question propositions of §8. However, there are two genuine (repairable) technical gaps, one false auxiliary claim inside the proof of the fundamental lemma, a recurring overclaim in the abstract/introduction relative to what Proposition 8.4 actually proves, and a structural editorial problem: the paper simultaneously claims self-containedness and defers several proofs to an unpublished companion manuscript that the reviewer cannot consult. All are fixable without disturbing the architecture; none is cosmetic enough to waive.

---

## 1. Summary of the paper

The paper extends a companion translation (CIC⁻ fragment → untyped classical FOL, factored through Letouzey-style erasure, proved sound against a single proof-irrelevant term model with junk) to *indexed inductive families*. The mechanism is McBride's fording, used as a lens in three places: the source calculus CIC⁻ix has a forded dependent case (branches bind proofs of the index equations) plus an elimination `scase` for "forced singletons" and a primitive `discr`; the emitted theory represents a family by a (1+m)-ary guard predicate, constructor-typing axioms with index conclusions, and a guarded inversion axiom whose disjuncts carry constructor payloads *and* index equations; the model interprets a family as a set of (index-tuple, element) pairs built in stages, with an *index reflection* lemma (unique constructor decomposition + index uniqueness + rank descent) as the semantic content of fording. Soundness is model-theoretic: every emitted axiom holds in one fixed structure 𝔐, so FOL-provability of the translated goal implies truth in a proof-irrelevant classical semantics, and the emitted theory is consistent by construction.

The second half (§8) settles design questions as theorems: per-occurrence expansion of guard atoms is sound in both polarities and logically inert; the inversion guard is not merely necessary but its omission is *inconsistent* for families that specialise an index to a constructor form (and detonates by cardinality for enumeration-shaped families); dropping the index arguments of guard predicates reproduces the F\* #1542 unsoundness inside the framework; unguarded per-constructor match equations are valid even at statically impossible branches, index-premised variants are sound but strictly weaker (two nontrivial countermodels), pruning is sound; index uniqueness is a first-order consequence while type-former injectivity is inexpressible-by-design (Hur); and the unconditional singleton collapse is exactly where the model's UIP is spent, with Werner's guarded reduction as the premise-carrying alternative.

## 2. Overall evaluation

**Significance.** The per-family axiom *shapes* (constructor typing + guarded inversion with index equations) are not new artifacts — Isabelle's `.cases` rules and F\*'s inversion axioms have this shape, as the paper says. The contribution is (i) the uniform one-model soundness discipline extended to families, which yields consistency of the whole emitted theory for free and lets a single semantic object arbitrate every guard question; (ii) the index-reflection lemma and element ranks, which make recursion over families go through with strikingly little machinery; and (iii) the negative results, which are genuinely valuable for implementers: the *inconsistency* (not mere unsoundness) of unguarded inversion sharpens the Meng–Paulson/Blanchette exhaustiveness folklore, Proposition 8.6 is a precise in-framework reconstruction of a documented production unsoundness, and the strictness results (Props. 8.9, 8.15) are proved via two carefully constructed countermodels — the "witness repair" κ for `vhead` and the {0,1}/XOR structure — whose necessity (pointer axioms tie defined symbols to the applicative structure of the domain, so pointwise reinterpretation is unavailable) is a subtle observation, correctly handled both times. §8 reads as a specification for implementations, which is exactly what this literature has lacked.

**Correctness.** I checked in detail: rigidity (Lem. 3.9) and derivable injectivity (Lem. 3.11, including the constant-motive construction against the `vtail` example); the erasure lemmas (4.6, 4.7); confluence (App. A — one missing subcase, M2); well-foundedness of the stage construction; index reflection (all five parts); adequacy and compilation soundness; coincidence; the fundamental lemma including the disciplined-spine, forded-case, fix (rank induction), `scase`, and induction cases; environment validity; and all of §8, including re-verifying both countermodels axiom by axiom and the inconsistency/pigeonhole derivations. Findings M1–M4 below; everything else stands up to adversarial reading.

**Fit.** Appropriate for a theory journal: rigorous, self-motivated, no empirical component (deliberately, and mostly honestly flagged — see M9). The writing is dense but precise, and the running examples are well chosen.

---

## 3. Major comments

### M1. The term translation 𝒞 is partial: □-headed application spines are unhandled (Def. 5.3)

`def:compC` (sections/translation.tex:77–124) defines 𝒞 on: the atomic forms x, □, 𝖼(ē); and application spines with head g (θ-bound), c (term-definition constant), x (variable), or a complex head (λ/case/fix). A spine headed by **□ itself** is covered by no clause, and it is reachable from well-typed sources: `efq(π; Πy:σ.τ) a` is well-typed, and its erasure is `□ ℰ(a)`. Concrete definition-level witness:

> c ≔ λp:⊥. λx:nat. efq(p; nat→nat) x  :  ⊥ → nat → nat erases to λx. □ x; compilation reaches rule (5) of Def. 5.4 with body □ x, and 𝒞(□ x) is undefined.

So Lemma 5.5's claim that the procedure "terminates on every input" (translation.tex:168–172), and the totality of 𝒢/ℱ on 𝔖 (Def. 5.7), are not established as stated. The repair is trivial and semantically forced: add the clause 𝒞_θ(□ e₁⋯e_j) = ⊙ @ 𝒞(e₁) @ ⋯ @ 𝒞(e_j), and the corresponding one-line case in Lemma 6.10 (adequacy: both sides denote [□ ê₁⋯ê_j]).

Relatedly, spines headed by a **constructor form** 𝖼(ē) e′ are also not covered. I believe these are unreachable from erasures of well-typed CIC⁻ix terms — rigidity (Lem. 3.9) prevents a constructor form from having a Π-type, and I could not manufacture one through `val`/`cast`/`scase` — but the paper should either state and prove that reachability invariant or add a clause. Note that 𝒞 is also invoked on goal-embedded terms, so the invariant must be phrased for every term the translation touches, not only definition bodies. (This gap is presumably inherited from the companion paper; it should be fixed there too.)

### M2. Missing subcase in the triangle lemma (App. A, Lem. A.4)

The case analysis in `lem:triangle` (confluence.tex:93–138) covers congruence clause (6) only "with non-constructor scrutinee", and the ι-redex clause (9). The subcase **step by congruence clause (6) on a case whose scrutinee is a constructor form** (i.e., the parallel step did not fire the ι-redex, but the development does) is not treated: there e = case(𝖼ᵢ(ē); br), e* = bᵢ*[ē*/x̄ᵢ], the step gives e′ = case(𝖼ᵢ(ē″); br′) (the scrutinee can only have reduced componentwise, via clause (5)), and one concludes by clause (9) with the componentwise induction hypotheses ē″ ⇒ ē* and bᵢ′ ⇒ bᵢ*. Routine — but the paper's stated standard is "all definitions and proofs in full", and this is exactly the kind of subcase (redex created by development but not by the step) that the Takahashi method exists to get right. Please add it.

### M3. A false auxiliary claim in the proof of the fundamental lemma (§7.2)

The preamble of the proof of Lemma 7.5 asserts (soundness.tex:127–130): "types, propositions and predicate expressions contain no applied occurrences of disciplined variables in well-formed judgements, by the same locality argument." This is **false**. If the fix type T_f has an index-typed codomain (say τ = nat), then a branch body may contain a well-formed type annotation such as λx:vect(f k w). … with w ∈ V_f — the occurrence of f is applied, inside a type, and satisfies the guard condition, so such terms are typable and respect the discipline. Nothing in the proof actually breaks: the semantics of types and propositions consumes only the *value* ρ(f) ∈ 𝒟 (index terms are evaluated by ⟦·⟧, never through a membership in the rank-restricted set), so no discipline obligation attaches to occurrences inside types. Replace the sentence by that observation. As it stands, the proof of the paper's central lemma contains a wrong statement, even if an unexploited one.

### M4. Bootstrapping of hypothesis (H) is circular as written (§7.2–7.3)

Lemma 7.5 fixes Ε and assumes (H) *for Ε* (soundness.tex:92–99). Theorem 7.6(1) then proves (H) by induction on declaration position, invoking Lemma 7.5 for a body typed over the *strict prefix* — but the lemma, as stated, requires (H) for all of Ε, which is what is being proved. The standard repair is one sentence: state Lemma 7.5 for an arbitrary well-formed definitional prefix Ε′ ⊑ Ε (or restrict (H) to the constants occurring in the derivation), and note that interpretations of phrases over Ε′ computed in Ε′ and in Ε agree, because Def. 6.2's recursion is by declaration position. In a paper whose selling point is full rigor, this bookkeeping should be exact.

### M5. Abstract and introduction overclaim Proposition 8.4

Prop. 8.4 (`prop:unguarded-inconsistent`) requires the constructor-headed index term to belong to a datatype **with a second constructor** — the hypothesis is stated precisely, and Remark 8.5 correctly says it "delimits the blast radius". But the abstract (main.tex:53–56: "for families that specialise indices to constructor forms its omission is *inconsistent*"), contributions item 6 (intro.tex:183–188: "for **every** family that specialises an index to a constructor form"), and §2.4 (fording.tex:176–181) all drop the side condition. A family indexed over a single-constructor datatype (e.g. a unit-indexed family with index pattern 𝗍𝗍) escapes both the clash argument and the cardinality argument: the unguarded axiom there is unsound (false in 𝔐 at junk) but not inconsistent. Either add the caveat in the three prose locations, or complement the proposition with a satisfiability proof for the single-constructor-index case so the delimitation becomes an exact dichotomy (the latter would be a nice strengthening and looks easy: interpret everything into a degenerate structure).

### M6. Self-containedness vs. the unpublished companion

The paper claims "all definitions and proofs are given in full, including the parts shared with the companion paper" (intro.tex:121–124), yet several proofs are by-reference: Lemma 3.10 ("Routine … exactly as in [Extraction2026]"), Lemma 6.10 ("exactly as in [§5.4]"), parts of Lemma 6.11, the quantifier/connective bullets of Lemma 6.13, and §7's predicate-axiom cases ("exactly as in [Extraction2026]"). Since [Extraction2026] is an *unpublished companion manuscript* (references.bib:1–6, with an empty author field — BibTeX warns), a referee cannot check the claimed correspondence, and the new formers make some of these non-trivial: the substitution lemma's `scase` case (commutation of the solution substitution θ with an ambient substitution) and `discr` case deserve their displayed one-paragraph arguments to be genuine proofs rather than parenthetical remarks — as it happens the parentheticals in Lemma 3.10 *are* the interesting content, so this is nearly done; say so and own it. Recommendation: (a) make the four lemmas above genuinely self-contained (each needs at most half a page), and (b) provide the companion as supplementary material or an arXiv identifier; the current citation is not checkable.

### M7. The CIC → CIC⁻ix front end is informal, and the end-to-end guarantee should say so in one place

Soundness begins at CIC⁻ix. The front end — stratification, monomorphisation, production of *forded* branches by inversion-style elaboration, dropping proof-sorted index positions — is described in §3.6 and §1.5 but is not part of any theorem, and the two case styles are intertranslatable only in CIC + UIP (§3.6, citing Goguen–McBride–McKinna). Consequently the operational reading "no refutable goal becomes provable" (Cor. 7.9) is relative to CIC⁻ix-refutability; a Rocq user needs the front end to reflect CIC-refutability into the fragment, and that step silently absorbs UIP on the source side, matching the model's validation of UIP on the target side. This is all implicitly present (§1.4, §9, §11.6), but scattered. Please add a short explicit paragraph — ideally at the end of §1.4 — stating the composed guarantee and its two assumptions (meaning-preserving front end; reconstruction as final arbiter). I am *not* asking for the front end to be formalised; only for the conditionality of the end-to-end claim to be stated once, sharply.

### M8. Remark 5.6 (`rem:eq-shape`) misdescribes the equation shapes

The claim that all LHSs have the form f(π̄) @ x₁ @ ⋯ @ x_k with π̄ constructor patterns *and the @-tail variables* is not what Def. 5.4 produces in general: rule (2) may refine a variable that was appended by rule (1) — branch bodies that are λ-abstractions followed by a case on the new variable — yielding constructor patterns in @-positions, e.g. f(Ô) @ 𝖼̂(z̄) ≐ …. Left-linearity and pairwise non-overlap (per head symbol, via the refinement partition tree) survive, so the orthogonality conclusion and everything downstream stand; but the stated shape is wrong. Fix the remark (and check the companion's twin remark).

### M9. Operational claims are qualitative; add the (easy) size accounting and one worked derivation

§8's verdicts are deliberately "the choice is operational" — good. But three places assert operational judgements with no support: the existential-residue remark (expansion "reasonable default" boundaries), Remark 8.11 (index premises are a "reconstruction-signal nicety"), and ex:reflect-expansion ("one resolution step more, contingent on premise selection"). Two cheap improvements: (i) state the formula-size bound for expansion variants (one level, so |𝒳_I| is linear in Σᵢ(rᵢ+ℓᵢ+m), per occurrence — worth displaying, since "shallow" translations have historically died of blowup); (ii) work one small derivation at the clause level (e.g. the goal `vhead (vcons k a w) = a` under the spec and inversion axioms, or the §8.1 reflect example done as a resolution trace) so the reader sees the advertised prover behaviour once. A full empirical study is rightly out of scope, but a sentence saying so explicitly would be honest (the current text implies it only via "idealisation", §1.5).

---

## 4. Minor comments

1. **grd wording (fig:terms2 caption, calculus.tex:478–481).** "requires every occurrence of f in b to occur in a subterm of the form f a₁⋯a_n" is satisfied by *any* occurrence inside such a subterm (e.g. f as an argument of itself). Def. 7.4 has it right ("lies at the head of an application spine"); align the caption.
2. **Forced singletons vs. Brady-style forcing (Def. 3.6, Rem. 3.8, related.tex:38–45).** Def. 3.6 requires forced variables to occur *verbatim* among the indices; Brady et al.'s forcing (and Gilbert et al.'s criterion) also count pattern-forced arguments (x under S in an index, recoverable by injectivity). Your `scase` is thus strictly between CIC's parameter criterion and the Gilbert et al. criterion, while §10's "extended from 'parameters put aside' to forced arguments" suggests the full notion. Semantically the pattern-forced generalisation looks available (index reflection on the index datatype recovers the argument class), but θ would no longer be a syntactic substitution. Add a sentence distinguishing verbatim-forced from pattern-forced and noting the generalisation as future work — or claim less in §10.
3. **(H)-independence of prefixes** (see M4) is also silently used in Rem. 7.11 (postulates) — the "evident extension of 𝔐" deserves one clause saying constructor and compiled-symbol interpretations are unchanged.
4. **Notation collision:** Φ is the fix-lift naming function (Def. 5.1), the schematic formula of Lemma 5.10, and the bijection of Prop. 7.10. Rename at least one.
5. **Def. 6.9 (model):** compiled symbols are interpreted "closure arguments first", but case-lift symbols have signature g(z, w̄′) with the extension argument first. Harmless, but state the convention per symbol or reorder.
6. **ex:eq-pred (translation.tex:480–484):** the displayed specification has ∀w before the eq-premise; Def. 5.8's recursion produces the premise first. Prenex-equivalent, but display what the definition emits.
7. **Def. 3.4:** the constructor-scheme format forces all premises after all informative arguments; CIC constructors whose *later argument types* mention an earlier proof argument (proof subterms in index terms of subsequent arguments) have no direct image. Harmless under proof irrelevance, but it is a fragment restriction — add it to §11.7's list.
8. **§11.7:** the list of syntactic exclusions omits function-space recursive arguments (A_ij = σ → I(v̄), infinitary constructors / W-types) — Def. 3.4 only allows direct recursive occurrences. State it.
9. **ex:running-axioms, the 𝗅𝖾 case-analysis display (translation.tex:432–439):** parenthesise the two existential disjuncts; as typeset, the scope of the first ∃n over ∨ is ambiguous.
10. **"∀." universal-closure notation** (first used in Def. 5.4 rule (3)) is never introduced.
11. **Def. 6.2:** it might be worth a footnote that ⟦I⟧ ⊆ ⟦σ̄⟧ × 𝒟 is *not* built into the stages and *not* needed anywhere (index tuples are never required to inhabit their index types) — a reader will look for this invariant; you avoid needing it, which is itself informative and very much in the spirit of the paper.
12. **Abstract** is ~1 page; most journals will ask for ≤250 words. The current abstract is really a contributions list.
13. **Metadata:** \author{} is empty and \date{AI draft of \today} must be resolved before submission; [Extraction2026] needs an identifier (see M6); BibTeX warns "empty author in Extraction2026".
14. **Related work (suggestions, not demands):** consider citing agda2atp (Bove, Dybjer, Sicard-Ramírez) as the closest Agda-side FOL translation; SMTCoq (Armand et al. 2011 / Ekici et al. 2017) for the certificate-based Coq↔solver route, to contrast with model-theoretic soundness; and the saturation-with-induction line (Hajdú–Kovács et al.) where §11.4 discusses not emitting induction.
15. **§9 S2's** "the one production system emitting inversion axioms with index equations for type-level families" is a strong uniqueness claim about a moving target; soften ("to our knowledge").
16. Build is clean (75 pp., no undefined references, no overfull warnings of note). I found no typos on a full read; the doubled-word and TODO scans are clean.

---

## 5. Questions for the authors

**Q1.** Is the extra permissiveness of Def. 3.6 beyond CIC's criterion (Rem. 3.8's example with non-uniformly instantiated recursive premises) ever *produced* by the intended front end, or is it purely robustness margin? If the latter, saying so would defuse the reconstruction worry of §11.6 further.

**Q2.** Prop. 8.10 declines to claim conservativity of pruning, with the caveat that a derivation "may in principle route through junk instances of a pruned equation." Do you have a concrete instance, or is this conjectural? If conjectural, a sentence saying "we do not know whether pruning is conservative" would be sharper than the current hedge; if you can prove non-conservativity by example, that is a nice result.

**Q3.** In Prop. 8.9's countermodel, the choice of κ (dead branch repaired to 𝖮) generalises: the moral paragraph claims the premised theory cannot distinguish the program from *any* repair of its dead code. Can this be made a theorem (a family of models indexed by repairs), or does the spec axiom constrain some repairs? Even a remark would strengthen §8.3.

**Q4.** §11.4 sketches a completeness theorem for the ground equational fragment over purely structural families "by standard rewriting arguments". Given Prop. 7.10 and Rem. 5.6 (as corrected per M8), this looks within reach of this paper; is there an obstruction I am missing? Its inclusion would substantially strengthen the operational story.

**Q5.** Def. 3.4 allows index *types* to be arbitrary closed set types, including Π-types — so families indexed by functions are in the fragment, with intensional index equality. Was this intended? It is sound (everything routes through class equality), but perhaps worth an example or a warning, since function-indexed families are exactly where the intensionality caveat (Rem. 8.16) bites hardest.

---

## 6. Assessment against journal criteria

- **Correctness:** main results correct; two repairable gaps (M1, M2), one false-but-unexploited in-proof claim (M3), one presentational circularity (M4). All fixable locally.
- **Significance:** solid. The one-model discipline for indexed families, index reflection, and the §8 negative results justify publication; the countermodels are the technical highlight.
- **Novelty:** the axiom shapes are folklore; the soundness discipline, the inconsistency sharpening, the F\*#1542 reconstruction, and the strictness countermodels are new as theorems.
- **Presentation:** dense but disciplined; excellent running examples; overclaims at the prose level (M5, §10's forcing claim) need aligning with the theorems; abstract too long.
- **Reproducibility/checkability:** blocked on the unpublished companion (M6) — the single most important editorial fix.

**Summary for the editors.** A strong, careful paper marred by a handful of local gaps and prose-level overclaims, and by its dependence on an unavailable companion manuscript. I expect the authors can address everything in one revision cycle; I would be happy to review the revision.
