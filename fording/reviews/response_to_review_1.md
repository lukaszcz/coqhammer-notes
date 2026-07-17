# Response to Referee Report (Round 1)

**Manuscript:** *Fording: A Sound Shallow Translation of Indexed Inductive Families into First-Order Logic*

We thank the reviewer for an exceptionally careful reading. All major and
minor comments have been addressed; the questions Q1–Q5 are answered below
and, where appropriate, in the text. Theorem numbers below refer to the
revised manuscript. One reply (M5) reports a mathematical correction to the
reviewer's proposed repair, which we hope is of interest: the dichotomy is
sharper than suggested, in the direction of a *stronger* theorem.

## Major comments

**M1 (𝒞 is partial on □-headed spines).** Fixed as suggested, and slightly
more. Def. 5.2 (`def:compC`) now has two additional head clauses:
𝒞_θ(□ e₁⋯e_j) = ⊙ @ 𝒞(e₁) @ ⋯ @ 𝒞(e_j), and the analogous clause for
constructor-form heads 𝖼(ē) e₁⋯e_j. The definition now closes with an
explicit exhaustiveness note, and a new Remark 5.3 (`rem:box-head`)
displays the reviewer's `efq`-based witness showing the □-headed clause is
*reachable*, records our belief (via rigidity) that constructor-headed
spines are not reachable from typed erasures, and explains why we add the
clause anyway: 𝒞 is invoked on goal-embedded terms, so relying on
unreachability would require a typing invariant at every invocation site,
whereas totality is free. Lemma 5.4 (termination) and the totality of 𝒢/ℱ
(Def. 5.8) are now unconditional; the adequacy lemma (Lemma 6.11) gains the
two corresponding cases (in its now fully written-out proof, cf. M6). We
have noted the same gap for the companion manuscript and will repair it
there identically.

**M2 (missing triangle-lemma subcase).** Added to Lemma A.4 as its own
bullet: the parallel step by congruence clause (6) on a case with
constructor-form scrutinee, where the development fires the ι-redex. The
argument is exactly as the reviewer sketches (scrutinee reduces
componentwise by clause (5) since no other clause matches its shape;
conclude by clause (9) with the componentwise induction hypotheses), with a
remark that this is the redex-created-by-development configuration the
Takahashi method exists for.

**M3 (false auxiliary claim in the fundamental lemma).** The false sentence
is deleted and replaced by the correct observation, essentially in the
reviewer's words: occurrences of disciplined variables inside types,
propositions and predicate expressions *do exist* (the reviewer's
λx:vec(f k w) example is now displayed in the proof preamble) and incur no
obligation, because every semantic clause consumes embedded terms only
through ⟦·⟧, which is defined for every valuation; rank-restricted
membership of ρ(f) is consulted only where the lemma's conclusion demands
it for a term or proof judgement.

**M4 (circular bootstrapping of (H)).** Repaired by the reviewer's first
suggestion. The hypothesis is now (H_{Ε′}), parameterised by a well-formed
prefix Ε′ ⊑ Ε; the fundamental lemma (Lemma 7.6) is stated for judgements
derivable over Ε′ assuming (H_{Ε′}); the §7.2 preamble states explicitly
that all semantic machinery is constructed once over the full Ε and is
(H)-independent, that Ε′-derivations are verbatim Ε-derivations
(Ε′-conversion ⊆ Ε-conversion), and that the proof consults the hypothesis
only in the constant cases. Theorem 7.8(1) now proves (H_{Ε′}) for every
prefix by induction on its length, invoking the lemma at the strict prefix
— no circularity. Corollary 7.11 cites the instance Ε′ = Ε explicitly.

**M5 (abstract/introduction overclaim of the inconsistency result).** Here
we must report that checking the reviewer's proposed delimitation led to a
*strengthening* rather than a caveat. The suggested satisfiability proof
for the single-constructor-index case does not exist in general: the
unguarded inversion axiom of **any** family with m ≥ 1 indices, together
with the family's *own* injectivity and discrimination axioms, first-order
derives ∀z z′. z ≈ z′ — the universe collapses. (The derivation is
precisely that of index uniqueness, Prop. 8.16, with the guard atoms
replaced by instances of the unguarded axiom: two instances at the same
element w and arbitrary tuples z̄, z̄′ pin the constructor witnesses by
injectivity, whence the index equations identify z̄ with z̄′
componentwise.) Consequently the unguarded axiom is inconsistent as soon
as the environment declares *any* two-constructor datatype — no
constructor-headed index pattern is needed; in particular the reviewer's
unit-indexed family with pattern 𝗍𝗍 is also inconsistent in any
environment containing 𝗇𝖺𝗍, since z ≈ t̂t is forced for all z. Proposition
8.7 is restated accordingly, in three parts: (1) the collapse; (2) its
corollary, including that a two-constructor family detonates on its own
axioms; (3) the previous clash argument, retained because it needs only
discrimination (no injectivity), with the vec instantiation. Remark 8.8
now gives the *exact* delimitation: since (1) derives total collapse, the
variant theory is consistent iff it has a one-element model; any
discrimination axiom refutes that, and the environment {U, F} with
mk : ∀y:U. F(tt) realises it (verified axiom by axiom) — while the axiom
remains false in 𝔐 even there, at the junk class [tt tt]. The abstract,
contributions item 6 and §2.4 are rewritten to the strengthened claim,
which is now *accurate* rather than an overclaim. The cardinality
mechanism for enumeration-shaped families is retained as the third comment
of Remark 8.8.

**M6 (self-containedness vs. the companion).** All four proof sites are
now genuinely self-contained: Lemma 3.12 (substitution) has a full proof
with the scase θ-commutation displayed as an equation and the discr case
argued explicitly; Lemma 6.11 (adequacy) is proved case by case, including
the two new M1 cases; Lemma 6.12's proof is de-referenced and its
root/rule-(2) steps expanded; the quantifier/connective/refinement bullets
of Lemma 6.13 are written out; and the predicate clause and case-analysis
cases of Theorem 7.8 are proved in full (stage argument and coincidence,
one level down). Remaining citations to the companion are provenance
notes, and the contributions preamble now says exactly that. The
[Extraction2026] entry now carries an author and the note that the
companion is provided as supplementary material with this submission.

**M7 (end-to-end guarantee).** Added as a labelled closing paragraph of
§1.3 ("The end-to-end guarantee, stated once"): the composed claim, its
two assumptions (meaning-preserving front end reflecting CIC-refutability,
absorbing UIP on the source side; reconstruction as final arbiter), the
pointer to Goguen–McBride–McKinna for the intertranslation, and the
explicit statement that neither assumption is formalised here.

**M8 (equation shapes).** Remark 5.6 is rewritten: the general left-hand
side is f(π̄) @ π′₁ @ ⋯ @ π′_k with constructor patterns possible in
@-positions (with the rule-(2)-refines-a-rule-(1)-variable mechanism and
the f(Ô) @ ĉ(z̄) example), and non-overlap is now *argued* via the
refinement-tree/divergent-split invariant, including the cross-@-depth
and pointer-axiom cases, rather than asserted.

**M9 (operational claims).** (i) The existential-residue remark (now
"Existential residue and size") displays the formula-size bound for 𝒳_I —
linear in the translated declaration, per occurrence, not iterable — with
the historical motivation made explicit. (ii) Example 8.5 now contains a
four-step clause-level refutation of the reflect view goal from the atomic
translation, showing exactly which resolution step (and which
premise-selection dependency) expansion removes. (iii) The example closes
with an explicit statement that no benchmark evaluation is included and
why. Remark 8.14's "reconstruction-signal" sentence is now backed by the
same honesty (see also Q2).

## Minor comments

1. **grd caption**: aligned with Def. 7.4 ("lie at the head of an
   application spine ... occurring as a subterm of b"), with the
   f-as-argument reading explicitly excluded.
2. **Verbatim- vs. pattern-forced**: Remark 3.9 now names the two notions,
   places scase strictly between CIC's parameter criterion and the Gilbert
   et al. criterion, and records the pattern-forced generalisation (θ no
   longer syntactic) as future work; §10's sentence is corrected to
   "verbatim-forced" with the same delimitation.
3. **Rem. 7.13 (postulates)**: the "evident extension" now says
   constructor and compiled-symbol interpretations are given by the same
   clauses with the same witnesses, and why validity arguments are
   unaffected.
4. **Φ collision**: the schematic formula of Lemma 5.15 is now Ψ; the
   bijection in Prop. 7.12's proof is now enc; Φ(·) remains only as the
   naming function of Def. 5.1.
5. **Def. 6.9**: the argument-order convention is stated per symbol kind,
   with the case-lift order (extension place first) displayed.
6. **ex:eq-pred**: the specification is displayed in the order Def. 5.9
   emits (premise before ∀w), with a note saying so.
7. **Premise-after-arguments restriction**: added to §11.7.
8. **Function-space recursive arguments / W-types**: added to §11.7.
9. **le case-analysis display**: both existential disjuncts are now
   parenthesised.
10. **∀. notation**: introduced in the preamble of Def. 5.3.
11. **Def. 6.3**: footnote added saying the invariant ⟦I⟧ ⊆ ⟦σ̄⟧ × 𝒟 is
    neither built in nor needed, and why that is informative.
12. **Abstract**: rewritten at ~250 words.
13. **Metadata**: author set, placeholder date removed, [Extraction2026]
    has an author and an availability note (BibTeX warning gone).
14. **Related work**: agda2atp (Bove–Dybjer–Sicard-Ramírez, FoSSaCS 2012)
    and SMTCoq (Armand et al. 2011; Ekici et al. 2017) added to §10 with a
    contrast of the certificate and model-theoretic disciplines; the
    saturation-with-induction line (Reger–Voronkov 2019; Hajdú et al.
    2022) is cited in §11.4, with the observation that the guarded
    induction schema of a declared family is true in 𝔐 (it is the
    semantic content of the datatype-induction case of the fundamental
    lemma), so prover-side induction composes soundly.
15. **§9 S2**: softened to "to our knowledge".
16. (No action needed; we additionally eliminated the handful of >10pt
    overfull lines in the figures and displays.)

## Questions

**Q1.** Robustness margin. The intended front end elaborates CIC singleton
eliminations, whose images satisfy the parameter criterion; it never
produces the extra permissiveness of Def. 3.6. This is now stated in
Remark 3.9, with the consequence that the corresponding reconstruction
obligation of §11.6 is expected to be vacuous in the pipeline.

**Q2.** Conjectural, and now stated as such. Remark 8.14 says explicitly
that we do not know whether pruning is conservative: no goal is known to
us whose derivation requires a junk instance of a pruned equation, and no
separating countermodel is available either (we indicate why the
witness-repair technique does not immediately apply). Pruning is justified
operationally, not semantically.

**Q3.** Yes — it is now Remark 8.13: for *every* closed repair e₀ of the
dead branch, the witness-reinterpreted structure satisfies Δ^π (each
verification step of the proof is checked to be repair-independent), and
v̂head(d, [vnil]) consequently ranges over all of 𝒟 across models of Δ^π.
The premised theory determines nothing about dead code; the unguarded
theory pins it to ⊙. The spec axiom constrains no repair, its guard
quantifying over genuine members only.

**Q4.** We agree it is within reach, but not by a corollary-length
argument, and we prefer not to include a rushed proof. §11.4 now states
the missing piece exactly: a simulation-and-standardisation development
relating the emitted orthogonal rewrite system to λ□ conversion on
compiled images. The paper proves no normalisation or standardisation
theorem for λ□ (deliberately — nothing else needs one), and
conversion-under-binders of lifted symbols is precisely what the emitted
equations do not reflect; for ground structural goals the under-binder
steps should be avoidable along a weak-head standard reduction, which is
the actual content behind "standard rewriting arguments". We consider
this a worthwhile follow-up rather than a revision item.

**Q5.** Intended, and now flagged. New Remark 3.5 (function-indexed
families) states that Π-typed indices are deliberately in the fragment,
that index equality then means conversion-class equality, and that this
is exactly where the intensionality caveat bites: extensionally equal but
non-convertible indices give disjoint, unrelated apertures, so transports
across them are soundly out of reach. Cross-referenced with Remark 8.19.

## Other changes

- The abstract, contributions and §2.4 now state the strengthened
  inconsistency theorem (see M5); no prose claim now exceeds a proved
  statement.
- Page count grew from 75 to 85, almost entirely from the inlined proofs
  (M6) and the new delimitation/repair-family material (M5, Q3).
