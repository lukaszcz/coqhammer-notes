# Response to Referee Report, Round 2

**Manuscript:** *Fording: A Sound Shallow Translation of Indexed Inductive Families into First-Order Logic*
**Date:** 2026-07-17

We thank the reviewer for an extraordinary report: the round-2 verification not only caught a genuine soundness-critical defect in the compilation layer (N1) but came with complete witnesses, the failing model computations, a delimitation of the blast radius, and a repair sketch whose coherence obligations the reviewer had already checked. This made the revision far faster and safer than it would otherwise have been. We are also grateful for the generous framing of the round-1 verification scope; we read the M6 episode the same way — the self-containedness policy surfacing exactly the kind of gap that compact by-reference arguments hide — and we have added the sanity invariant the reviewer proposed so that this particular class of gap cannot go quiet again.

**Cross-references.** All numbering in this letter is that of the revised manuscript, read off the final build (we have double-checked every citation below against the compiled PDF, in response to the numbering-drift note in §1 of the report). One shift to be aware of: two new items were inserted in §5 after Lemma 5.5 (Lemma 5.6, Remark 5.7), so the round-2 report's "Remark 5.6" (equation shapes) is now **Remark 5.8**; every other number the report cites (Definitions 5.1, 5.2, 5.4, Remark 5.3, Lemma 5.5, Definition 6.10, Lemmas 6.11–6.13, Theorems 7.8–7.9, Corollaries 7.10–7.11, Example 8.5, Proposition 8.7, Remark 8.8) is unchanged.

---

## 1. The major issue N1: fix variables leaking into lifted closures

**Accepted in full, and repaired.** The reviewer is right on every count: the closure clauses of Definition 5.2 and rule (3) of Definition 5.4 took `w̄ = fv(h)` with nothing excluding θ-bound recursion variables; the universal closure then quantified the very argument place the model-side witness dereferences; W1 (conditional recursion on a computed test) and W2 (a recursive closure passed to a higher-order function) are ordinary, well-typed, guarded, shallow programs that reach the configuration; and under the naming convention of the old Definition 5.1 the collision of N1b yields an outright inconsistent emitted theory, contradicting Corollary 7.10 as stated. We have verified the reviewer's two witnesses and the N1b chain independently and agree with the blast-radius analysis (no §8 result and no worked example is affected; the semantic half is untouched).

### 1.1 The repair as implemented

We adopted **route 1 (pointer-value pinning) uniformly**, at the root as well as at inner fix-lifts, rather than mixing routes 1 and 2. Route 2 (definiens substitution) would work at roots, but a single mechanism keeps Definition 5.2's three lift clauses parallel, and the root instance of pinning is degenerate anyway (`val_θ(g₀) = ĉ⁰`, a constant). The components:

1. **Pointer values and pinned closures (Definition 5.2 and its preamble).** Every template symbol has an associated pointer (`ĉ⁰` for the root — which exists, since a fix root has `a_c = m ≥ 1`, the guard argument being informative; `Φ⁰(·)` for a fix-lift), and `val_θ(g) := f⁰(w̄)` for `θ(g) = (f, w̄, m)`. Every lift (λ-, case-, and fix-) now uses the *pinned* closure — θ-bound members replaced by their pointer values — in the value, in the emitted rule-(3) equation, **and in the recursion left-hand side**, exactly as the reviewer's parenthetical warned was necessary. The pointer axiom of a fix-lift is stated over fresh variables (it is valid at *every* closure value, both symbols interpreting through the shared witness, so it needs no pinning; this also preserves the all-variable pointer left-hand sides that Remark 5.8's non-overlap argument uses).

2. **Naming keys (Definition 5.1).** The naming functions Λ, X, Φ, Φ⁰ are now injective on **pairs `(h, θ↾fv(h))`** — the lifted term together with the restriction of the template map to its free variables — up to consistent renaming of free variables (the restriction's domain renamed along). Definition 5.1 also states why this is well defined: the axioms attached to a lifted symbol are computed from this pair alone, the procedure consulting θ only at variables free in the lifted term (the recursive B-calls at lifts carry `θ↾fv(h)`, so this is enforced structurally, not just observed). This dissolves N1b and also the reviewer's α-copy-with-different-templates variant: two structurally recursive definitions sharing a closure shape but differing in template content now key differently. We chose the pair over a substituted "θ-resolved term" because for inner fix-lifts there is no closed syntactic resolvent to substitute without growing the input (the reviewer's own observation about the termination measure), and the pair is exactly the data the emissions depend on. (This also answers **Q2**; see §3.)

3. **Template refinement under rule (2) (Definition 5.4).** While working through the repair we found that pinning and keying alone do not close the gap: there is a **sibling configuration, not requiring any θ-bound variable in a closure**, in which rule (2) refines an *ordinary* variable stored in a template closure and the stored template drifts off the refined left-hand side. Witness (now the second example of Remark 5.7):

       c′ := λb:bool. fix f:(Πn:nat. vec(n) → nat). λn v.
               case(v; {vnil ⇒ O | vcons(k,a,w) ⇒ case(b; {true ⇒ f k w | false ⇒ a})})

   The inner fix-lift has closure `(b)` and template `(Φ, (b), 2)`; the branch case on `b` — a variable of the left-hand side — is refined by rule (2); the true-leaf then compiles `f k w` through the *stored* template and would emit `∀. Φ(true, n, vcons(k,a,w)) ≈ Φ(b, k, w)` with `b` universally quantified on the right but absent from the left — false in 𝔐 at junk values of `b` by the same witness computation as N1's. This is the reviewer's diagnosed root cause ("B's output depends on θ while the naming key does not") manifesting through rule (2) rather than through the key. The repair: **rule (2) applies its substitution to every closure term stored in θ, together with L** (Definition 5.4, rule (2)). The true-leaf then emits `∀n k a w. Φ(true, n, vcons(k,a,w)) ≈ Φ(true, k, w)` — the recursion correctly specialised — and the coherence transfer in Lemma 6.12's rule-(2) case is the first-order substitution lemma applied to the stored templates. (Note the substitution into pinned subterms *of L* is automatic — they are subterms — so the point of the clause is exactly the stored map.) With this third component, the reviewer's remark that left-hand sides may fail left-linearity "when w̄_g-variables repeat elsewhere in L" is accommodated soundly: the repeated occurrences are refined simultaneously and consistently.

### 1.2 The reviewer's consequence checklist

Each consequence the reviewer listed for route 1 is worked out where predicted:

- **Definition 6.10 (coherence)** gains exactly the clause the reviewer checked: `⟦val_θ(g)⟧_ρ = [σ_θ(g)]` (clause (1); the old condition is clause (2)), plus the requirement that the closure terms' variables be assigned by ρ. The definition now records which clause serves which consumer (lifts consume (1), the template clause of 𝒞 consumes (2)).
- **Lemma 6.12, statement (1)** is now quantified *per assignment*: "for every call and every assignment ρ there is σ_θ …". This also repairs a latent misstatement of the previous version (∃σ∀ρ), which was already untenable for inner fix-lifts, where σ_θ(g₀) is the closed witness instance at the closure *values* and hence ρ-dependent.
- **Lemma 6.12, proof**: coherence is now established *uniformly* — define σ_θ(g) as a closed representative of `⟦val_θ(g)⟧_ρ = (f⁰)^𝔐(⟦w̄⟧_ρ)`; clause (1) holds by construction, and clause (2) follows because `f` and `f⁰` carry the *same* witness (the constant c at the root, the fix term h at a fix-lift). The reviewer's two establishment-site checks (root: `(ĉ⁰)^𝔐 = [c]`; fix-lift: the closed witness instance) appear as the two instances of this one argument. The rule-(2) case gains the template-transfer sentence; the rule-(3) and rule-(4) cases consume clause (1) at the pinned places; the fix-lift pointer-axiom case notes validity at *arbitrary* (junk included) closure values via the shared witness.
- **Lemma 6.11 (adequacy)**: the complex-head bullet is rewritten around the pinned closure — the denotation of a pinned place is `[σ_θ(g)]` by coherence clause (1), so substituting representatives effects exactly `(·)^{ρ,σ_θ}`. The sentence the reviewer flagged ("the closure parameters receiving the values ρ assigns them", which was undefined at θ-bound parameters) is gone; the new text says explicitly that this is where pinning earns its keep, ρ assigning nothing to a θ-bound variable.
- **Remark 5.8 (was 5.6): equation shapes.** The left-hand-side grammar now includes pinned closure terms (`π ::= x | ĉ(π̄) | f⁰(π̄)`), with constructor patterns entering pinned terms through rule (2). The non-overlap argument is extended as the reviewer indicated: rule-(2) splits act simultaneously at every occurrence of the split variable, each occurrence position is rigid in the persisted L₀-instance (constructor and pointer symbols have fixed arities), and pinned subterms create no new overlaps because no left-hand side is pointer-headed at its spine bottom while pointer axioms keep their all-variable, ⋈-rooted left-hand sides. **Left-linearity may now fail** (a variable inside a pinned term may recur elsewhere in L); the remark states this openly: the oriented system is orthogonal on the fragment without recursive closures and non-overlapping in general, with duplicated variables confined to pinned positions. The one downstream citation of orthogonality (§11.4, the ground-completeness discussion) is weakened to match ("non-overlapping … orthogonal in the absence of recursive closures"); S5 of §9 claimed only non-overlap and needed no change.
- **The sanity invariant** the reviewer suggested is **Lemma 5.6** (*Emitted axioms are sentences over ordinary variables*): θ-bound variables occur in no emitted formula; the proof runs the invariant that left-hand sides and stored closure terms stay over ordinary variables through every rule. Definition 5.1's closing line ("source term variables double as first-order variables") now carries the corresponding exclusion, addressing the report's "either way" fork explicitly: θ-bound variables are *not* first-order variables of the emitted theory, and the formulas are sentences.
- **The reachability record** the reviewer suggested is **Remark 5.7** (*Recursive closures: reachable, pinned, keyed*): it exhibits W1 in full with its pinned emissions, shows the false instantiation (junk at the f-place, [vnil] at w) that the unpinned reading would validate, sketches the N1b collision and its resolution by keys, gives the template-refinement witness of §1.1(3), and notes the λ-closure variant (W2's shape). No totality or well-formedness claim in §5 now rests on an unreachability belief; Remark 5.3's closing sentence — the report's minor 6 — is rewritten to say precisely this, crediting the head clauses *and* the pinning discipline jointly for unconditional totality, instead of asserting what N1 refuted.

### 1.3 Honesty about provenance

Since the compilation layer is advertised as the companion's, §5.2's preamble and contribution item 3 of §1.2 now state that the present formulation *repairs* the companion's treatment of recursive closures and that the repair is to be read back into the companion (with Remark 5.7 as the pointer). We considered it wrong to present the repaired clauses silently as if they had always been the companion's.

---

## 2. Minor comments on the revision

1. **Metadata — done, genuinely this time, and with an apology.** The round-1 response claim was inaccurate: only the bibliography entry had been fixed, and `main.tex` still carried the placeholders. The blank author was an oversight, not double-blinding. The revision sets the author (Łukasz Czajka) and a proper date; the placeholder is gone. We have re-checked the compiled title page.
2. **Response-letter numbering.** Acknowledged; this letter cites final compiled numbering throughout (see the note at the top, including the one §5 shift).
3. **Proposition 8.7(1), degenerate case — added.** The proof now opens with the constructor-less clause: `Inv⁻_I` is then the universal closure of the empty disjunction, i.e. of ⊥, so the collapse — indeed anything — follows outright, and the case analysis proceeds under "at least one constructor".
4. **Example 8.5, displayed goal — annotated.** The displayed goal now says "(the carrier guard `b̂ool(b)` contributed by the bool-quantifier is elided; it plays no role in the refutation)".
5. **Abstract length — trimmed.** The abstract is now 255 words (from ~290), with no claim added or dropped.
6. **Remark 5.3's closing sentence — revisited** as part of the N1 repair; see §1.2, last bullet.

---

## 3. Questions

**Q1 (companion manuscript).** Yes on both counts. The companion's compilation has the same `w̄ = fv(h)` closure clauses and the same term-keyed naming convention, and its fragment does admit W1/W2-shaped witnesses (computed-scrutinee cases and higher-order arguments are both within it; the witnesses do not use indexing at all — W1's use of `vec` is decorative, and a `list`- or `nat`-valued variant triggers the same configuration). The companion is being amended identically in this revision cycle, and the amended version will accompany the resubmission as the supplementary material. The clause list there is exactly: pinned closures in the three lift clauses and the rule-(3) emission; template refinement under rule (2); keyed naming; the sentence-hood lemma; plus the two head clauses of Definition 5.2 that our round-1 M1 note already flagged as inherited. Its adequacy and compilation-soundness lemmas take the same two-clause coherence definition and the same uniform establishment argument (the shared-witness observation is fragment-independent).

**Q2 (domain of the naming functions).** Pairs `(h, θ↾fv(h))`, up to consistent renaming of free variables, now stated normatively in Definition 5.1 rather than left informal — together with the fact that makes hash-consing well defined (emissions are a function of the key). We preferred the pair to a θ-resolved term for the reason sketched in §1.1(2): at inner fix-lifts resolution would substitute a fix term and grow the input, disturbing the termination measure of Lemma 5.5, whereas the pair is finite syntactic data with no effect on the measure.

**Q3 (implemented translation).** Confirmed, and now said in §5: the closing sentence of Remark 5.7 records that practical λ-lifters, the implemented translation included, substitute the symbol introduced for a fixpoint for its recursion variable before closures are computed — pointer substitution — so N1 was a defect of the formal development, not a production unsoundness. The formal pinning discipline makes the development match that practice rather than diverge from it.

---

## 4. Summary of changes (by location)

- **Definition 5.1**: naming-function domain fixed to `(h, θ↾fv(h))` up to consistent renaming; well-definedness of hash-consing recorded; recursion variables excluded from first-order variables of emitted formulas.
- **§5.2 preamble**: templates' closure terms; pointers `ĉ⁰`/`Φ⁰`; `val_θ`; pinned lists; the standing facts about θ-bound occurrences (spine heads only; never in emitted formulas). Provenance note about the repair relative to the companion.
- **Definition 5.2**: all three value-translation clauses pinned; naming keys; θ restricted to `fv(h)` in lift recursions; fix-lift pointer axiom over fresh variables; root-fix pointer existence note in Definition 5.4's initialisation.
- **Definition 5.4**: contract rephrased (left-hand-side variables now include stored-template variables; linearity moved to Remark 5.8); rule (2) refines θ; rule (3) pins.
- **Lemma 5.5**: measure clarified (first-order data outside the measure); merging by keys.
- **Lemma 5.6 (new)**: emitted axioms are sentences over ordinary variables.
- **Remark 5.7 (new)**: reachability witnesses, the pinned emissions, the N1b collision, the template-refinement witness, the implementation note.
- **Remark 5.8 (was 5.6)**: left-hand-side grammar with pinned terms; extended non-overlap argument; left-linearity caveat and delimited orthogonality.
- **Remark 5.3**: closing sentence rewritten (minor 6).
- **§1.2 item 3**: repair flagged as a delta over the companion.
- **Definition 6.10**: coherence clause (1) added; closure-variable coverage required.
- **Lemma 6.11**: complex-head bullet rewritten around pinned closures (flagged sentence removed).
- **Lemma 6.12**: statement per-assignment; uniform coherence establishment via shared witnesses; rule-(2) template transfer; rule-(3)/(4) via clause (1); pointer-axiom validity at arbitrary closure values.
- **§11.4**: orthogonality citation weakened to non-overlap (orthogonal on the closure-free fragment).
- **Proposition 8.7**: degenerate clause (minor 3). **Example 8.5**: guard elision note (minor 4). **Abstract**: 255 words (minor 5). **main.tex**: author and date (minor 1).

The build is clean: no errors, no undefined references or citations, BibTeX silent, all remaining overfull boxes below 10pt (none in the newly edited §5 material).
