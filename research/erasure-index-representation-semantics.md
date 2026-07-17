# Research report: erasure and index-representation semantics for indexed inductive families

*Produced by a web-research agent, 2026-07-16, for `notes/indexed_families.md`.
Primary PDFs archived in `../papers/` where available.*

---

## 1. Letouzey's extraction

**Citations.** *A New Extraction for Coq*, TYPES 2002, LNCS 2646. PhD thesis,
Univ. Paris-Sud, 2004 (HAL tel-00150912; download bot-blocked — reconstructed
from the papers). *Extraction in Coq: an Overview*, CiE 2008, LNCS 5028.

**The erasure function** (TYPES 2002, Def. 1, 3, 5). Target CIC□ = CIC plus
one *untyped*, irreducible constant □. E is defined by:

> (□) If t is a type scheme or has sort Prop in context Γ, then E_Γ(t) = □.

Otherwise purely structural. E is a **pruning**: "it only replaces some
sub-terms by □. In particular no modification of the structure can occur."
The old rule E([x:P]t) = E(t) for P:Prop is rejected (changes evaluation
order; the `False_rec` partial-application example). Ad-hoc □-reduction
`(□ u) →□ □` absorbs applications of erased functions.

**Singleton elimination (extraction side).** A logical `Cases` can produce
informative content only when the eliminated logical inductive has:

> "1. zero constructor (empty inductive, like False), or
> 2. one constructor whose arguments are all logical, **parameters put
> aside** (singleton inductive, like eq)."

Annotated singleton matches get `<...>Cases_n □ of f end →ι f □ ... □`.
Soundness (Appendix A): in an assumption-free context the scrutinee reduces
to (C p̄ v̄) with all vᵢ logical — singleton elimination is erasable *because
everything the branch could learn from the proof is itself erased*. Two
documented hazards: (i) **strong reduction of singleton elimination is
unsound** (the `cast : nat==bool → nat → bool` example — under reduction
under lambdas an integer lands where a boolean is expected; weak/closed
reduction is saved by canonicity); (ii) **fixpoints with logical guards**
(Acc): dropping the guard check makes E(loop) diverge; the fixed ι-rule fires
only "if u_{k_i} is equal to □ or begins with a constructor".

**Correctness.** The invariant ◄ (Def. 10) + weak-reduction simulation both
ways (Thm 12/13); Thm 15 for closed terms of logic-free data-types.
Restrictions: **no axioms** ("we may lose the fundamental fact that a closed
inductive term will necessarily reduce to a term beginning with a
constructor"). The thesis adds "a semantical study based on realizability
(§2.4)" to cope with axioms — the analogue of CoqHammer's model-based
argument.

**sig and singleton optimization.** In core E, `exist` merely loses its proof
argument; the collapse to the carrier is a separate *optimization* (§4):
"(exist x) is isomorphic to x". CiE'08: `sumbool` extracts to a bool-like
two-constant type; informative `{x:A | P x}` vs logical `∃x, P x`.

**Indexed families.** Erasure is purely **sort-directed**; no forcing/index
analysis. Indices-as-types vanish into □; value indices *stored as
constructor arguments* (the length in `vcons`) are informative and **kept**
even though redundant; a Prop-sorted indexed family (`le`) erases wholesale.
CiE'08 is explicit that even a "morally useless" kept counter cannot be
removed automatically.

**Relevance.** (a) Under extraction the entire information content of a
Prop-sorted indexed family lives in its *type*, which is erased — the
first-order equational content of the indices is exactly what a FOL
translation must re-materialize; Letouzey says when the proof object is dead,
not which equations replace it. (b) □ is a single global canonical proof
token: the precedent for `$Proof`; its syntactic soundness regime is weak
reduction + closed terms + no axioms; beyond that only the realizability/
model semantics applies. (c) His erasability criterion leaves indices
syntactically unrestricted *because extraction's branch is index-blind* — a
translation that keeps index equations needs the sharper analyses below.

---

## 2. Brady, McBride, McKinna — *Inductive Families Need Not Store Their Indices* (TYPES 2003)

**Citation.** LNCS 3085, pp. 115–129. Extended: Brady's PhD thesis (Durham,
2005). PDF read from an e-pig.org mirror (`indfam.pdf`, archived).

**Setting.** TT + Dybjer families; eliminators implemented by pattern
matching with *presupposed* patterns (matched without testing). The standard
implementation "comments out the indices — just as well, because there is no
guarantee that they generally take the constructor form which explicit
matching requires." An optimisation = substitution on
constructors/eliminators + ExTT ι-schemes (deleted terms {t}, deleted tags
{c}), required to be Γ-well-defined and Γ-respectful modulo a substitution
recovering deleted variables.

**The three criteria — exact definitions.**

- **Forceable**: "Whenever c ā, c b̄ : D s̄ implies aᵢ = bᵢ, the i-th argument
  of c is forceable." **Concretely forceable**: expressing the result-type
  indices s̄ as patterns, "any aᵢ appearing as a pattern variable in p̄ is
  forceable, by injectivity of constructors … retrieved **in constant time by
  pattern matching on the indices**." Forcing deletes such arguments from
  stored constructors (e.g. both A and k in `:: : ∀A k a v. Vect A k → Vect A
  (s k)`).
- **Detaggable**: "If c ā, c′ b̄ : D s̄ implies c = c′." **Concretely
  detaggable**: with *eager* index patterns, distinct constructors' index
  patterns are pairwise disjoint — the tag is deleted, case selection happens
  on an index (Vect: 0 vs s k).
- **Collapsible**: "If x, y : D s̄ implies x = y." **Concretely collapsible**:
  detaggable + constructor tag and all non-recursive arguments cheaply
  recoverable from the indices. Then the family vanishes at run time
  entirely.

**Run-time-only status.** Collapsing is invalid in open contexts ("not
respectful and breaks subject reduction"); "In a partial evaluation setting …
we run the risk of reducing a proof of something which cannot be constructed,
such as 5≤4!" Justified at run time by **adequacy**: closed inhabitants WHNF
to constructors.

**Semantic vs concrete.** The `Compare` family is collapsible but not
*concretely* collapsible (recovery would require recomputing a difference) —
semantic index-determinacy is deliberately separated from the syntactic,
unification-based criterion licensing the optimisation.

**Punchlines.** `≤` collapses entirely; Bove–Capretta accessibility
predicates are concretely collapsible — "Collapsing replaces computation over
qsAcc by computation over its indices, restoring the intended operational
semantics"; conclusion verbatim: "deleting accessibility arguments and all
the equational reasoning from run-time code, **not because we deem them to be
proof-irrelevant, but because they actually are**."

**Relevance.** (a) This is the precise semantics of "the index equations
determine the erased data": an argument is erasable iff the equations
s̄ = constructor-result-indices determine it. What forcing/detagging/
collapsing *delete*, a FOL translation can *re-derive* from the emitted index
equations. (b) They never canonicalize a proof inside an index — deletion
requires unique determination up to definitional matching (cf. Compare).
(c) Collapsibility is the exact semantic criterion for "this indexed family
is pure index-constraint and can be erased outright"; concrete collapsibility
is its decidable approximation. The 5≤4 warning marks the boundary: erasure
reasoning is valid only where canonicity holds — a hammer translation must
argue soundness model-theoretically instead.

---

## 3. QTT and Idris 2 erasure

**Citations.** Atkey, *Syntax and Semantics of Quantitative Type Theory*,
LICS 2018. Brady, *Idris 2: Quantitative Type Theory in Practice*, ECOOP
2021 (arXiv:2104.00480). Precursor: McBride, *I Got Plenty o' Nuttin'*, 2016.

**The system.** Usage annotations ρ from a positive semiring; "a variable
with usage 0 has no 'run-time' presence, **but may still be used in the
formation of types**"; all type formation happens in 0-contexts; the σ=0
fragment is ordinary MLTT.

**Semantic guarantee.** Quantitative CwFs realized over R-Linear Combinatory
Algebras with `!₀x = !₀y` for all x, y: "ensures that we have a canonical
representation of erased data in our models." Realisers of well-typed
programs provably cannot depend on 0-arguments. **Erasure holds by
construction of the model, which interprets all erased data by one canonical
element — a direct formal cousin of a `$Proof` constant, generalized from
proofs to arbitrary 0-used data.**

**Idris 2 practice.** "An argument with multiplicity 0 is guaranteed to be
erased at run time … still relevant at compile time." Indices erased iff
0-quantified; an erased index cannot flow to run time (the RLE/`Singleton xs`
example); pattern matching on 0-arguments only where *forced* by relevant
patterns. §5.3 situates against Brady et al. 2004 forcing/collapsing and
Idris 1's whole-program erasure inference (Tejiščák; also his ICFP 2020
erasure-inference calculus).

**Relevance.** (a) QTT decouples "is an index" from "is erased": erasing
indexed-family *proofs* is orthogonal to erasing the *indices* — index
equations may mention perfectly relevant terms. (b) `!₀x = !₀y` is the
algebraic form of "one canonical token for all erased things"; it justifies a
single global `$Proof` provided nothing relevant inspects it. (c) The
discipline "erased things may appear only where nothing relevant can observe
them; the observation that would distinguish them (index unification on
proof-built indices) is exactly the UIP/K-flavored step."

---

## 4. sProp and Agda — Gilbert, Cockx, Sozeau, Tabareau, POPL 2019

**Citation.** *Definitional Proof-Irrelevance without K*, PACMPL 3(POPL):3,
2019. Agda docs on `Prop` and run-time irrelevance.

**Framing.** "Proof-irrelevance … is at the heart of the Coq extraction
mechanism." Their diagnosis of Coq's singleton elimination: "the fundamental
misunderstanding that singleton elimination was the right constraint …
**singleton elimination does not work for indexed datatypes, for instance …
the equality type of Coq**. If proof irrelevance holds for the equality type,
every equality has at most one proof, which is known as Uniqueness of
Identity Proofs. Therefore, assuming proof irrelevance together with the
singleton elimination enforces a new axiom in the theory … incompatible with
the univalence axiom." §2.2 makes the mechanism exact via the contractible
singleton `Sing A a`: eliminable-with-PI ⟹ propositional equality collapses
into definitional equality ⟹ ETT/UIP/undecidability.

**Acc.** Satisfies singleton elimination but definitional PI for it makes
conversion undecidable: the `Acc_rect` unfolding can be replayed forever —
the recursion is "*semantically* guarded by the R y x condition", not
syntactically. (Lean's closed-term compromise "breaks in particular subject
reduction".)

**Forced arguments and the corrected criterion.** ≤ (with `≤0 : ∀n, 0 ≤ n`,
`≤S : ∀ m n, m ≤ n → S m ≤ S n`) is eliminable although it fails singleton
elimination: "**A forced argument is an argument that can be deduced from the
indices of the return type of the constructor**" (terminology from Brady et
al. 2004) — m, n in ≤S are forced; only the non-forced `m ≤ n` must be
propositional. The stdlib-style `≤bad` (refl/step) is *not* eliminable: "in
the (absurd) context that e : S n ≤bad n, there are two ways to form a term
of type S n ≤bad S n … allowing m ≤bad n to be eliminated into any type would
require to decide whether the context is absurd." The criterion (§2.4): an
sProp inductive may be eliminated into arbitrary types iff

> (1) every non-forced argument is in sProp;
> (2) the return types of constructors are pairwise orthogonal (indices
>     non-unifiable);
> (3) every recursive call satisfies a syntactic guard condition.

Justification (§5): translate the inductive to a **fixpoint over the indices
computed by a case tree**, elaborated with proof-relevant unification; the
elaboration constraints `w /? v` are index equations; dead branches are
`sEmpty` (e.g. `S _ ≤fix 0 := sEmpty`).

**Metatheory.** Predicative sMLTT: syntactic translation to ETT with
mere-proposition interpretation; impredicative sProp needs propositional
resizing, "justified by any classical model of ETT … every mere proposition
is either sEmpty or Unit." Strict propositional equality in sProp "implies
uniqueness of identity proofs" (consistency by adding UIP — "already observed
by Werner [2008]"). Implementations: Coq's SProp allows only *empty*
inductives to eliminate into relevant values; Agda's run-time irrelevance
forbids matching on erased arguments "unless there is at most one valid case.
When --without-K is enabled … the constructor's type must not be indexed" —
the without-K refinement exists precisely because matching an erased
scrutinee of an *indexed* type extracts index-unification information whose
validity requires K/UIP.

**Relevance.** (c) The sharpest criterion for which indexed families admit
erasure-with-elimination: non-forced args proof-only + pairwise-orthogonal
constructor index patterns + guard. `eq` is exactly the boundary case: its
index is a forced variable pattern, so eliminating it transfers a conversion
y ≔ x; PI there = UIP. (a) The case-tree translation *is* "the family as a
function of its indices defined by index constraints" — the constraints are
literally the index equations CoqHammer plans to emit; the sEmpty branches
are the negative content. (b) An index term `f x p` with p a proof makes p
non-forced, so the criterion forces p : sProp, and definitional PI makes
`f x p ≡ f x q` — canonicalization to a token is conversion-valid in sProp
and semantically valid in any proof-irrelevant model; ≤bad is the standing
warning that in absurd contexts index equations can identify things no
constructor justifies (harmless for provability-soundness, fatal for
decidable conversion).

---

## 5. Proof-irrelevance models and MetaCoq verified erasure

**Models.**
- Werner, *Sets in Types, Types in Sets*, TACS 1997: set-theoretic model of
  CIC in ZF + inaccessibles, Prop collapsed.
- Lee & Werner, *Proof-irrelevant model of CC with predicative induction and
  judgmental equality*, LMCS 7(4:05), 2011: "The only way to provide a
  set-theoretic meaning for an impredicative proposition type is to identify
  all the proof terms of that proposition type: **Proposition types are
  interpreted either by the empty set or a singleton with a canonical
  element.**" Validates judgmental PI; inductive families via Aczel rule
  sets; ZF + ω inaccessibles. Such models validate PI, UIP, EM; incompatible
  with univalence. (Also Barras, *Sets in Coq, Coq in Sets*, JFR 2010.)
- Werner, *On the Strength of Proof-Irrelevant Type Theories*, LMCS 4(3:13)
  2008: conversion quotiented by an extraction relation "quite close to
  Letouzey's"; with PI, UIP "becomes trivial"; PI + choice ⇒ decidable
  equality. See §6 for its index-condition content.

**MetaCoq.** Sozeau, Boulier, Forster, Tabareau, Winterhalter, *Coq Coq
Correct!*, POPL 2020; extended JACM 2025 (*Correct and Complete Type Checking
and Certified Erasure for Coq, in Coq*; paywalled). Target λ□ with `tBox`;
evaluation amendments verbatim: "(1) If a ▷ □ then (tApp a t) ▷ □. (2) If
a ▷ □ then eCase (i,p) a [(n,t)] ▷ t □…□. (3) The rule for tFix is extended
to also apply if the principal argument evaluates to □." — Letouzey's three
□-rules, mechanized. Erasability (`Extract.v`):

```
Definition isErasable Σ Γ t :=
  ∑ T, Σ ;;; Γ |- t : T ×
  (isArity T + (∑ u, (Σ ;;; Γ |- T : tSort u) * Sort.is_propositional u)).
```

The tCase/tProj erasure rules carry the side condition today called
`Subsingleton` (`PCUICElimination.v`): whenever a constructor application of
the family is a proof (in any well-formed extension of the environment), the
family has ≤ 1 constructor and all non-parameter constructor arguments are
proofs — the mechanized singleton criterion is *semantic* and stable under
environment extension. "Theorem 4.7 (Erasure Correctness)": weak CBV
simulation up to the erasure relation; functional on first-order inductive
types (Lemma 4.8, separate compilation Cor. 4.8.2). Assumptions: axiom_free;
Prop ≤ Type disabled. Future work verbatim: "Letouzey [2004] introduces a
semantic account of erasure correctness, which would allow the treatment of
axioms." On sProp: "adapting erasure is almost trivial." The development
"relies only on axioms on the metatheory and on **proof irrelevance**".

**Relevance.** (a) The mechanized pipeline confirms: indices never survive
erasure, redundant value arguments do, and case-on-proof is admissible only
under Subsingleton — a translation keeping index equations works strictly
outside what verified erasure preserves and must be justified against a
model. (b) `tBox` + rules (1)–(3) is the operational spec of a canonical
proof token. (c) `Subsingleton`, quantified over environment extensions, is
the robust semantic form of the singleton criterion.

---

## 6. Index terms mentioning proofs; when is `p ↦ $Proof` inside an index sound?

**Werner 2008 is the key text** (§2.4–2.5). In a theory where all equality
proofs are convertible, naive singleton reduction is unsound: "we cannot rely
on the information given by the equality proof e … allowing, for any e, the
reduction (Eq_rec A P a b p e) ⊲ p is too permissive, since **it easily
breaks the subject reduction property in incoherent contexts**." His repair
keeps the erased proof's information as an *index-convertibility side
condition*:

> (Eq_rec A P a b p e) ⊲ p **if a =ε b**

(the non-linear alternative breaks Church–Rosser via Klop's counterexample).
Generalized (§2.5) to any Coq-singleton inductive with constructor
c : Π ȳ:B̄. I ū: reduce `(I_rec X p ā i) ⊲ (p ε̄)` **"if ū =βε ā"** — erase the
proof, canonicalize erased constructor arguments to the tag ε, keep the index
equation as the guard. This is almost literally the guarded-erasure
decomposition read as a reduction system; Werner needs it *definitionally*
(SR + decidability), a model-checked translation only needs the equation
*provable* — weaker and safe.

**Assembled answer to "when is `f x p ↦ f x $Proof` sound?"**
- *Semantically*: in any proof-irrelevant model (Werner 1997, Lee–Werner
  2011, Atkey's !₀-LCA), all proofs of a proposition denote one canonical
  element, so ⟦f x p⟧ = ⟦f x $Proof⟧ on the nose — for any f, even junk model
  functions — provided `$Proof` denotes that element. That PI is only
  propositional in CIC is irrelevant for a translation verified against a PI
  model.
- *Definitionally*: only under sProp/PI-conversion; there the criterion
  forces any proof inside an index term (non-forced, non-pattern) into
  sProp — already canonicalized by conversion. Coq-sProp, Agda @0, Idris 2
  quantity-0 all encode the same rule: **erased proofs may appear in index
  terms only where nothing relevant can observe them; the observation that
  would distinguish them is exactly the UIP/K-flavored step.**
- *UIP connection*: canonicalizing proofs inside indices of an equality-like
  family is equivalent in strength to UIP (Gilbert et al. §2.2/§4.4; Werner
  2008). Justification must come from a model validating UIP — set-theoretic
  proof-irrelevant models do; univalent ones do not. A junk/total PI model is
  on the right side of the line.
- *Boundary cases*: Brady's "5≤4" and Gilbert's ≤bad both concern
  open/inconsistent contexts, where index equations derived from constructor
  result types may be contradictory. Benign for provability-soundness (an
  inconsistent context proves everything), but index equations must be
  emitted as *guarded, per-occurrence* facts, never unconditional global
  axioms about the family.
- Related: Barras–Bernardo (ICC*, FoSSaCS 2008), Mishra-Linger–Sheard
  (EPTS, FoSSaCS 2008), Tejiščák (ICFP 2020).

---

## 7. Singleton elimination in Coq/Rocq — the official criterion

**Citation.** Rocq reference manual, *Theory of inductive definitions →
Destructors* (source `inductive.rst` read).

For I : Prop the base rule allows elimination only into SProp/Prop, because
informative elimination "implies that there are two proofs of the same
property which are provably different, **contradicting the proof-irrelevance
property**". Extension:

> I empty or singleton ⟹ elimination into any sort. "A *singleton definition*
> has only one constructor and **all the arguments of this constructor have
> type Prop**. In that case, there is a canonical way to interpret the
> informative extraction on an object in that type … Typical examples are the
> conjunction of non-informative propositions and the equality."

Parameters are not "arguments" (Letouzey's "parameters put aside"); SProp
arguments also allowed. SProp inductives must be *empty* to eliminate into
relevant values. Non-qualifying inductives are "squashed". Unsorted
inductives are placed in the smallest sort permitting large elimination.

**Why eq qualifies**: `eq_refl` has zero real arguments; the result index is
the forced variable pattern `x`, so a Type-sorted match on `h : x = y`
transfers precisely the conversion y ≔ x — "index unification as the entire
computational content," which is why extraction reduces the match blindly on
□, and why making the same move definitional yields UIP.

**Why Acc qualifies and matters**: one constructor whose single argument is a
Prop-valued product — the engine of well-founded recursion. Extraction keeps
the fixpoint guard discipline with □ standing in for the Acc proof
(Letouzey's loop; MetaCoq rule (3)); definitional PI for Acc is undecidable
(semantic guardedness); Lean's compromise breaks SR.

---

## Cross-cutting summary for the CoqHammer design

1. **Emitting per-constructor index equations is the logical mirror of
   forcing/case-tree elaboration.** Brady's forceable-by-index-matching and
   Gilbert's elaboration constraints `w /? v` are exactly "constructor c is
   witnessed iff indices = ū" — FO equations plus, from
   detagging/orthogonality, disequalities between distinct constructors'
   index patterns (the sEmpty branches). What their optimizations *delete*, a
   FOL translation *asserts*.
2. **`$Proof` has three independent precedents**: Letouzey/MetaCoq's □
   (operational), Atkey's !₀x = !₀y canonical erased realiser (algebraic),
   and the set-theoretic canonical proof element (denotational, Lee–Werner).
   The junk model is in the third, strongest regime — the only one that also
   survives axioms (Letouzey's syntactic theorems and MetaCoq both assume
   axiom-free environments and point to semantic accounts for axioms).
3. **Canonicalizing proofs inside index terms** is sound in any model
   interpreting all proofs by one canonical element denoted by `$Proof`;
   Werner 2008's guarded rule `(I_rec … ) ⊲ (p ε̄) if ū =βε ā` is the exact
   syntactic ancestor of the guarded-erasure decomposition. Known cost: UIP
   (already valid in a proof-irrelevant total model). Known danger zone:
   open/inconsistent contexts — index equations stay hypothesis-guarded per
   occurrence, never unconditional.
4. **Which families admit full erasure**: semantically, Brady's
   collapsibility (fibrewise mere-proposition-ness over indices);
   decidably, Gilbert's triple (non-forced args propositional,
   pairwise-orthogonal constructor index patterns, syntactic guard), which
   strictly extends Coq's official singleton rule and correctly rejects
   Acc-style semantic guardedness (needs its own guardrail) and ≤bad-style
   non-orthogonal indices. Presentation-sensitivity (≤ vs ≤bad; Compare)
   means the criterion must be checked on actual constructor result types,
   not up to propositional equivalence.
