# Research report: fording, dependent pattern-matching elimination, and FO axiomatization of index constraints

*Produced by a web-research agent, 2026-07-16, for `notes/indexed_families.md`.
Primary PDFs archived in `../papers/` where available.*

---

## 1. McBride's "fording" construction (1999 thesis)

**Citation.** Conor McBride, *Dependently Typed Functional Programs and their
Proofs*, PhD thesis, University of Edinburgh, 1999 (ECS-LFCS-00-419).

**Name origin.** §3.5 "scheming with constraints" opens with *"'You can have
any color you like, as long as it's black.' (Henry Ford)"* (p. 63): "in much
the same way that Henry Ford's customers could ask for any colour of Model T,
but would only receive satisfaction if they happened to choose black, the
above scheme is indeed abstracted over the entire aperture, but the patterns
to which it applies are subject to equational constraints which recover their
specificity."

**The construction.** In the thesis, fording is presented at the level of
*elimination schemes*: given an elimination rule proving a scheme Φ for
patterns ~p[~y] and a more specific goal ∀~x. Ψ[~p[~y]], choose the motive

    Φ = λ~ı. ∀~x. ~ı ≃ ~p[~y] → Ψ[~p[~y]]

— abstract the rule's full "aperture" ~ı and constrain it to the concrete
indices by a *telescopic equation* (pointwise sⱼ ≃ tⱼ). Instantiating the rule
and discharging the reflexive equations recovers the goal. Optimizations
(§3.5.1–3.5.3): coalescence (fresh ∀-variable constrained to equal an index is
merged, equation dropped — but if one variable equals *two* indices only one
coalescence is allowed or "we lose this 'diagonalisation'"), avoiding
redundant abstraction, simplifying complex patterns.

Worked example (§5.2, p. 128): `vtail : ∀n. vect (s n) → vect n` via
`vectCase` gets the constrained scheme
`λi. λx : vect i. ∀n. ∀v : vect (s n). i ≃ s n → x ≃ v → vect n`, giving for
`vnil` the impossible premise `0 ≃ s n` and for `vcons` hypotheses
`e₁ : s m ≃ s n, e₂ : x ≃ v`. This is exactly the ford of
`vcons : A → vec A m → vec A (S m)` into a constructor usable at an arbitrary
index.

**Heterogeneous/telescopic equality.** §3.5 (p. 65), §5.1.4: "we must be able
to express these constraints even in the presence of type dependency … we need
a notion of equality which scales to telescopes." Homogeneous `=` cannot even
*state* `v₁ = v₂` before `n₁ = n₂` is substituted. McBride's `≃` is
heterogeneous "John Major" equality (§5.1.3): formation `a : A, b : B ⊢ a ≃ b`,
only reflexive introduction, eliminator restricted to the "type diagonal".
The eliminator's strength is exactly J+K: heterogeneous `eqElim` ⟺ K
(McBride, *Elimination with a Motive*, TYPES 2000; stated explicitly in Cockx
ICFP'14).

**Datatype-level fording.** Modern statement (Tesla Zhang, *Two Tricks to
Trivialize Higher-Indexed Families*, arXiv:2309.14187, §4, attributing to the
thesis): a constructor `c : X → F a` fords to
`c_Ford : (a' : A) → (a = a') → X → F a'`, after which "F is no longer
indexed." E.g. `data So (b : Bool) | oh (b = true)` — "So b is nothing but a
wrapper of b = true." Zhang shows fording lets you *delay* index rewriting:
after fording, the equation is a first-class datum a consumer may use whenever
convenient — precisely the property a translation to ATPs wants. (Also:
*Custom Representations of Inductive Families*, arXiv:2505.21225.)

**Side conditions.** In type theory the forded equations need heterogeneous
equality (K-strength if eliminated) or homogeneous telescopic equality with
transports. In *untyped* FOL both problems evaporate: `≃` between arbitrary
terms is just `=` on the untyped universe, no transport needed. Under proof
irrelevance (the junk model) K is valid anyway, so heterogeneous equality
costs nothing semantically.

---

## 2. Goguen, McBride, McKinna 2006: Eliminating Dependent Pattern Matching

**Citation.** LNCS 4060 (Goguen Festschrift), pp. 521–540. Companion:
McBride, Goguen, McKinna, "A few constructions on constructors," TYPES 2004,
LNCS 3839.

**Result.** A reduction-preserving translation from Coquand-style dependent
pattern matching into UTT with inductive types **and axiom K**. Pattern
matching = valid *splitting trees*; each node case-splits on `x : D ~v` where
for every constructor `c(∆c) : D ~u`, first-order unification of `~u` with
`~v` must succeed positively (MGU σ) or negatively (conflict/cycle);
"first-order unification with datatype constructors as the rigid symbols."

**Machinery.** Heterogeneous `Eq` + `refl` + homogeneous-instance `subst`
(built from I, J, **K**). Per datatype: `caseD`, `BelowD`/`recD`
(course-of-values recursion), `noConfusionD` ("the proof that D's
constructors are injective and disjoint" — two-level:
`NoConfusionNat P (suc x) (suc y) ↦ (x ≃ y → P) → P` etc.), `noCycleD`
("disproves any cyclic equation in D").

**The five unification transitions (Lemma 16):**

- **deletion**: discharge `t ≃ t` (motive well-typedness is where K hides)
- **solution**: `t ≃ x` with x ∉ FV(t), via subst
- **injectivity**: `c ~s ≃ c ~t → P` reduces to `~s ≃ ~t → P` via noConfusion
- **conflict**: `c₁ ~s ≃ c₂ ~t → P` discharged outright
- **cycle**: `x ≃ c ~p[x] → P` discharged via noCycle

Termination: lexicographic (#variables, #constructor symbols, #equations);
complete for constructor forms. **Specialization by unification (Def. 19)**:
for eliminator at targets ~t, take motive `λΞ. Π∆. Ξ ≃ ~t → T`; for `caseD`
each method gets `m_c : Π∆c; ∆. ~u ≃ ~v → c ∆c ≃ x → T` — "the equations on
the indices are exactly those we must unify to allow the instantiation of x
with c ∆c." **This is fording of constructors, in print, in working form.**

**K accounting.** In GMM06 K-dependence is smeared over the whole development
(everything built over heterogeneous Eq). The sharp accounting is Cockx's:
deletion = K; injectivity at repeated/non-variable indices hides another K.

**Relevance to untyped FOL.** The five transitions are precisely the
first-order theory of constructors: deletion = reflexivity, solution =
paramodulation, injectivity/conflict = the injectivity/distinctness axioms,
cycle = acyclicity. GMM06 §4.1: the unification "becomes explicit equational
reasoning, step by step" — a proof-producing version of what a saturation
prover does natively. A FOL translation need not run unification at
translation time: emit forded equations + injectivity/distinctness (+
optionally acyclicity) and the ATP performs specialization-by-unification as
ordinary superposition. Completeness of the type-theoretic procedure holds
only for constructor-form indices; the ATP handles defined-function-headed
indices (green slime) *better* — it keeps `0 = plus m n` and may close the
branch using plus's defining equations, strictly more than elaboration-time
unification can.

---

## 3. Cockx, Devriese, Piessens (ICFP 2014) and Cockx & Devriese (JFP 2018)

**Citations.** "Pattern Matching Without K," ICFP 2014. "Proof-relevant
unification," JFP 28 (2018), e12. (Also "Unifiers as equivalences," ICFP 2017;
Cockx PhD thesis 2017.)

**ICFP 2014 — the K-free criterion.** Transitions: deletion `x = x, Θ ⇒ Θ`;
solution; injectivity `c s̄ = c t̄, Θ ⇒ s̄ = t̄, Θ`; conflict; cycle. K-freeness
restricts exactly two: **(1) deletion is forbidden; (2) injectivity on
`c s̄ = c t̄ : D ū` is allowed only if the indices ū are self-unifiable**
(unification of ū with itself succeeds positively under the same
restrictions). J is definable by matching; K is not (`a = a` needs deletion);
`weakK` is caught by self-unifiability (a real Agda `--without-K` soundness
bug); matching on `n ≤ n` is fine, but `i ≤ i` with `i : Fin n` is stuck
(over-conservative). Deletion is admissible K-freely at h-sets (Hedberg:
decidable equality ⇒ UIP).

**Why (§3.5).** With homogeneous telescopic equality
`(s; s̄) ≡ (t; t̄) := (e : s ≡ t)(ē : e∗ s̄ ≡ t̄)`, the transitions become
proof-relevant. Dependent deletion "is exactly the K axiom." Dependent
injectivity needs to eliminate reflexive index equations `ū ≡ ū` — "we cannot
eliminate the equations ū ≡ ū in general without using the K axiom."
Conflict and cycle escape because they *factor through ⊥* — the two negative
rules are K-free unconditionally; the positive rules are where K lives.
No-confusion must be a (half-)equivalence (`noConfD⁻¹` + left-inverse proof)
for the translated program to compute.

**JFP 2018.** Unification rules as *type equivalences between telescopes*
(Fig. 8): `solution : (x : A)(e : x ≡_A u) ≃ ()`;
`deletion : (e : u ≡_A u) ≃ ()` — **valid only for A satisfying UIP**
(Lemma 30); `injectivity_c` simplifies index equations and the constructor
equation *simultaneously*; `conflict`, `cycle` to ⊥. Notable:

- **Example 40**: for `data Im f : B → Set` with
  `image : (x : A) → Im f (f x)`, simultaneous injectivity solves
  `e₁ : f x ≡ f y, e₂ : image x ≡ image y` to `x ≡ y` even though
  `f x ≡ f y` alone is unsolvable — **the forded constructor equation is
  strictly stronger than the bare index equations**.
- **Counterexample 35**: conflict is only valid for *fully applied*
  constructors — `left ≡_{⊥→⊥⊎⊥} right` is NOT absurd under funext (Agda bug
  #1497).
- Generalized injectivity at arbitrary indices needs *UIP on the index
  telescope types* (Lemma 62): "we only moved [the problem] to the indices" —
  motivating higher-dimensional unification (§6.2), which removes UIP at the
  cost of substantial machinery. GMM06's structural order for cycle was also
  *wrong* for higher-order constructor arguments (fixed in Fig. 7).

**Relevance to untyped FOL.** Every K-difficulty is a proof-relevance
difficulty: in a proof-irrelevant classical target UIP holds in every model,
so **deletion, injectivity at non-linear indices, and heterogeneous equality
are all unconditionally sound** — the without-K literature is a catalogue of
obstacles the translation provably does not have. What it does force:
(i) conflict/discrimination axioms only for fully-applied data constructors
(Counterexample 35); (ii) injectivity axioms only for *data* constructors,
never inductive *type* constructors — type-constructor injectivity is
anti-classical (Chung-Kil Hur 2010: Agda + EM inconsistent via injective type
constructors); (iii) emit the constructor-level equation and let index
equations follow from injectivity, not the other way around (Example 40).

---

## 4. "Green slime"

**Primary source.** McBride, "How to Keep Your Neighbours in Order," ICFP
2014, §4, verbatim: "**The presence of 'green slime'—defined functions in the
return types of constructors—is a danger sign.**"

**Technical content** (thesis §5.4.1, pp. 149–151): constructor-form
unification is complete, but non-constructor-form indices (e.g.
`node X Y : stree (s (plus x y))`, or case analysis on `vect (plus m n)`)
leave *stuck* equations like `0 ≃ plus m n` — failure, not negative success,
because `plus` is not rigid. Type-level comparisons worse: "we do not have
theorems such as conflict at the level of types—we cannot disprove N ≃ 2."
Standard workarounds: (1) **ford the offending index into an equation**
(`c : ... → f x̄ = i → F i`); (2) re-express the function relationally /
recursion-induction (`plusRecI`; measures→requirements in the BST paper);
(3) derived elimination rules for the defined function.

**Relevance.** Green slime is a *decidability-of-elaboration* problem, not a
semantic one. A saturation prover given plus's defining equations,
injectivity/distinctness, and the forded constraint derives `m = 0 ∧ n = 0`
or refutes the branch — **in the FOL target, green slime dissolves into
ordinary equational reasoning**; the translation never solves index
constraints, only states them. Caveats: negative branches need distinctness
(and sometimes acyclicity) axioms; slime refutations are undecidable in
general — fording gives *completeness of expression*, not decidability.

---

## 5. Small inversion / derived inversion

**Citations.** Cornes & Terrasse, "Automating Inversion of Inductive
Predicates in Coq," TYPES 1995, LNCS 1158 (paywalled; reconstructed from
secondary sources). McBride, "Inverting Inductively Defined Relations in
LEGO," TYPES 1996, LNCS 1512. Monin, "Proof Trick: Small Inversions," Coq
Workshop 2010 (HAL inria-00489412). Monin & Shi, "Handcrafted Inversions Made
Operational on Operational Semantics," ITP 2013, LNCS 7998 (slides read).
Monin, "Small inversions for smaller inversions," TYPES 2022 abstract.

**Cornes–Terrasse / Coq's `inversion`.** Given `H : I ā`, generalize the goal
over the indices constrained by *equations* — prove `∀x̄, x̄ = ā → C` by case
analysis on fresh `I x̄`, then simplify `t̄ᵢ = ā` with injection/discriminate.
**This is fording performed on-the-fly at the use site.** The Rocq manual's
description of `dependent induction` says it verbatim: the hypothesis is
"generalized over its indexes which are then constrained by equalities."

**Does inversion need K? No.** The generated equations are homogeneous and
used non-dependently (the motive never depends on the equation proofs).
Monin 2010 implements inversion "just by dependent elimination with an
auxiliary diagonal function," with no equality type at all — hence trivially
no K. Where K sneaks in for Coq users: constructor arguments whose types
depend on other arguments produce `existT`-equalities; projecting them
(`inj_pair2`) is equivalent to K on the index type — avoidable via
`Eqdep_dec` (decidable equality) or `inversion_sigma`. This is the use-site
analogue of Cockx's "injectivity needs UIP on the indices."

Monin–Shi ITP'13: handcrafted CPS-style diagonal functions per constructor
shape; small proof terms, "no additional (proof of) equalities are
introduced"; motivated by CompCert-scale inductive relations where built-in
`inversion` produces unmanageable terms.

**Relevance.** An inversion principle is exactly the FOL sentence the
translation would emit for a forded family:
`∀m n. le(m,n) → (m = 0 ∧ …) ∨ (∃m'. n = s(m') ∧ le(m,m') …)`. Inversion is
derivable *without any axioms* inside CIC (Monin), so emitting guarded
inversion sentences is sound for the junk model; the `existT` wrinkle
disappears in untyped FOL (pair projections are function symbols) — but do
NOT emit projection of dependent-pair equalities as a general schema for
*type-level* second components (anti-classicality trap, §3).

---

## 6. Equations plugin — Sozeau & Mangin, "Equations Reloaded" (ICFP 2019)

**Citation.** PACMPL 3(ICFP), Article 86, 2019. (Earlier: Sozeau ITP 2010.)

**Pipeline.** Clauses → GMM06-style splitting tree → per-node simplification
of index/argument equations by an OCaml **simplification engine** producing
genuine Coq proof terms; per-datatype `Derive NoConfusion / NoConfusionHom /
Subterm / EqDec`. Exposed as `simplify` and `dependent elimination` ("a
robust replacement to the inversion tactic").

**Simplification steps (§4.4.1):** Remove-sigma (telescopic equality curried
into equalities-with-transport); **Deletion** `∀(e : t = t), P e ⇒ P eq_refl`
— "requires UIP … precisely the K principle, unless P does not actually
depend on e"; **NoCycleLeft/Right** — "implements the occur-check", NoCycle
instances derived "from any WellFounded relation, in particular derived
Subterm relations"; **SolutionLeft/Right** (uses J); **NoConfusion** (same
constructor → equalities of *non-forced* arguments only; distinct → False);
**Pack/Unpack** — heterogeneous fallback, "requires UIP on the type of the
indices, or it will fail." Exactly two steps can use UIP — Deletion and Pack —
both disabled unless `Equations With UIP`; UIP derivable from `EqDec`.

**Homogeneous no-confusion (§4.3) — their theoretical novelty.** Using
**forced-argument analysis** (Brady–McBride–McKinna 2004: the `n` in `cons`
is *forced* by the return index `S n`):
`NoConfHom_vector (cons a n v) (cons a' n v') := (a,v) = (a',v')` — compare
only within the same family instance, record only non-forced arguments;
K-free and computes on refl. **Derivability condition** (verbatim): "this
derivation will fail if equality of constructors in the inductive family
cannot be reduced to equalities of their non-forced arguments. Typically,
this is the case of equality [`eq` itself]: implementing homogeneous
no-confusion on equality would be equivalent to UIP … Other examples … any
non-linear use of an index … and constructor conclusions that do not fall
into the pattern subset [green slime] … The fact that NoConfusionHom is
derivable … ensures that one will never need UIP in pattern-matching problems
involving it — 'well-behaved index types'" (`fin`, `vector`, well-scoped
`term` all qualify).

**Relevance.** Equations is the closest artifact to "compile indexed matching
to non-indexed + equations" *inside* CIC, and its axiom accounting transfers:
with UIP available (junk model), *every* simplification step is sound,
including bare Deletion and Pack — a FOL translation may emit the unrestricted
rule images without the homogeneous/forced-argument refinements, which exist
only to *avoid* UIP. Forced-argument analysis remains useful as an
*optimization*: it identifies index equations that are redundant given
constructor injectivity (which forded equations may be omitted to reduce ATP
clutter). Their NoCycle-from-Subterm derivation mirrors the FOL acyclicity
schema.

---

## 7. Acyclicity / first-order axiomatization of term algebras

**In the pattern-matching literature**: cycle appears in thesis Table 5.1,
GMM06 Lemma 16 (`noCycleD`), Cockx ICFP'14 (K-free, factors through ⊥), JFP
Lemma 61 (with corrected structural order). Type-theoretic status: acyclicity
is a *theorem* (structural induction), never an axiom; needs no K.

**In FOL.** Kovács, Robillard, Voronkov, "Coming to Terms with Quantified
Reasoning," POPL 2017 (arXiv:1611.02908). The FO theory of the Σ-term algebra:

- (A1) domain closure / exhaustiveness: ⋁_f ∃ȳ (x ≈ f(ȳ))
- (A2) distinctness: f(x̄) ≉ g(ȳ), f ≠ g
- (A3) injectivity: f(x̄) ≈ f(ȳ) → x̄ ≈ ȳ
- (A4) acyclicity: schema t ≉ x for every non-variable t containing x

T_FT = (A1)–(A4) is complete and decidable (Mal'cev 1962; Maher LICS 1988;
Rybina–Voronkov 2001); non-elementary with arity > 1. **(A4) is not finitely
axiomatizable** — remedies: a finitely axiomatized conservative extension with
a subterm predicate `Sub(s,t)` (generation + transitivity + irreflexivity),
or prover-native rules (Vampire term-algebra rules; Robillard 2018). Crucial
caveat (Theorem 2): adding *uninterpreted* symbols makes the theory
Π₁¹-complete — with defined functions and guards in the signature,
completeness of the datatype fragment is gone; only refutational completeness
w.r.t. emitted axioms remains. SMT side: Barrett–Shikanian–Tinelli JSAT 2007
(occurs-check built into the decision procedure).

**Design flags.** (A2)/(A3) per data constructor: unconditionally sound in
the junk model — the cheap, high-value part. (A4): sound but choose bounded
instances / subterm-predicate extension / prover-native datatypes. (A1) is
where the junk model bites: the universe contains junk not generated by
constructors, so **unguarded (A1) is unsound**; the sound image of (A1) is the
*guarded inversion sentence* (`∀x. Guard_D(ī,x) → ⋁_c ∃… x = c(…) ∧
index-equations`) — Cornes–Terrasse in FOL clothing, and exactly what a
forded family's completeness amounts to. Off-the-shelf SMT datatypes build in
(A1) and so over-approximate CIC families.

---

## 8. Directly on translating dependent inductive types to FOL

Little beyond the hammer line itself: Czajka & Kaliszyk JAR 2018 (baseline);
Blot et al., "Compositional pre-processing for automated reasoning in
dependent type theory" (CPP 2023, arXiv:2204.02643) — Sniper/Trakt generates
injectivity/distinctness/"generation" (inversion) statements per inductive as
*Coq-proved lemmas* before SMT export; non-indexed or lightly-indexed only.
HOL formalizations routinely express `vec A n` as `{l : list A | length l = n}`
— **fording is the default in weaker logics**. No paper claims a "complete
first-order axiomatization of inductive families"; the compositional picture:
families = fording (McBride) + non-indexed inductives; the non-indexed theory
is complete-but-infinitely-axiomatized (§7) relativized by guards.
Completeness necessarily fails at (A4) and at induction; everything else —
injectivity, distinctness, guarded inversion, forded index equations — is
finitely axiomatizable per family.

---

## Cross-cutting synthesis

1. **Fording is exactly the right primitive and is fully general.** Every
   system surveyed — GMM06's basic analysis, Coq's inversion/`dependent
   induction`, Equations' splitting, Agda's unifier — already reduces indexed
   families to constructors-with-equality-constraints internally;
   datatype-level fording does it once at declaration. No source reports an
   inductive family that cannot be forded (HITs aside); green slime,
   non-linear indices, and `eq` itself all ford fine — they only break
   *unification-time solving*, which the translation intentionally does not
   do.
2. **All K/UIP obstructions are proof-relevance obstructions and vanish in a
   proof-irrelevant, classical, untyped target.** Deletion = K; injectivity
   at non-linear/defined indices = UIP-on-indices; heterogeneous-equality
   elimination = K. The junk model validates UIP, so the *unrestricted*
   GMM06 rule set is the correct semantic reference; the without-K refinement
   layer is citable as *unnecessary* for soundness — while forced-argument
   analysis is borrowable as an optimization (omit derivable index
   equations).
3. **FOL axiom images:** per data constructor: injectivity (A3) + pairwise
   distinctness (A2); per family: guarded inversion (the sound (A1));
   optionally acyclicity (A4) bounded/extended/native. Three traps: no
   injectivity for type constructors (anti-classical, Hur 2010); no conflict
   for under-applied constructors (funext, Counterexample 35); no unguarded
   exhaustiveness (junk model).
4. **Heterogeneous equality is trivial in untyped FOL** — McBride's
   motivation for `≃` is purely the inability of typed homogeneous `=` to
   state telescope equations before substitution, a constraint that does not
   exist untyped. Substantive addition rather than dissolution: simultaneous
   injectivity (Example 40, `Im f`) — the forded constructor equation is
   strictly stronger than the bare index equations; emit the constructor
   equation, derive index equations via injectivity.
