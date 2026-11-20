# Specification extraction for dependent inductive types

*Design note, 2026-08-31. Written as the question left open by
`notes/indexed_families.md` §2.3 and `notes/gaps.md`: the translation expands
exactly two shapes of inductive occurrence (`CSubset`, `CEnum`) into formulas a
prover can use directly, and leaves every other inductive as an opaque typing
atom. What does the general case actually get, why are those two special, and
what would it take to make the specification of an arbitrary dependent
inductive ATP-usable? §§1-7 below are a self-contained description of what the
code does today, written so that the proposal in §§8-11 has no undefined terms.
Sources, all read for this note: `src/plugin/coq_transl.ml`,
`src/plugin/coq_erasure.ml`/`.mli`, `src/plugin/coq_convert.ml`,
`src/plugin/coqterms.ml`, `src/plugin/coq_transl_opts.ml`,
`tests/plugin/check-extraction-transl.sh` (branch `fording`, Rocq 9.2).
Sibling notes: `notes/dependent_types.md`, `notes/extraction.md`,
`notes/indexed_families.md`, `notes/type_guards.md`, `notes/gaps.md`.
Nothing here was verified by running the translation; see §12.*

## TL;DR

1. The specification of a dependent inductive -- the content of its
   propositional constructor arguments -- is **never dropped**. It is emitted
   at declaration level, split across the constructor typing axioms
   (introduction) and the inversion axiom (elimination). §5.
2. It is **not ATP-usable in general**. At an occurrence `w : I p̄ ū` the
   translation emits the opaque atom `$HasType(w, I(p̄,ū))`; reaching the
   specification costs a resolution step against a generic inversion axiom
   plus reasoning under its Skolem functions. §6, §8.
3. The two expanded shapes are not ad-hoc. They are the two cases in which the
   body of the inversion axiom simplifies enough to be inlined at the
   occurrence: `CEnum` is "the existential binds nothing", `CSubset` is "the
   existential is solved by its own equation, and the constructor symbol
   disappears with it". §6.
4. **The general rule already exists** as `notes/indexed_families.md` §2.3's
   guard schema; what is missing is a termination discipline. Today's
   termination is structural, resting entirely on the side conditions of those
   two shapes -- there is no expansion-depth guard anywhere in the plugin
   (§9.2, verified). Adding an explicit one-constructor-layer bound is what
   makes the general rule well-defined.
5. Doing so is **in policy**: it needs no new symbols and no bridge axioms, only
   a generalized `guard_leaf`. Projection/selector symbols, which an earlier
   sketch of this proposal assumed were required, are probably **not** needed:
   specification extraction is a positive-position phenomenon, and there plain
   existentials Skolemize to constants. §9.3.
6. Suggested sequencing: Stage 1 (non-recursive families, all constructors) →
   Stage 2 (one-layer expansion for recursive families) → measure → Stage 3
   (selectors) only if the measurements demand it. §11.

Two defects found while writing this note, both independent of the proposal and
worth fixing regardless: a duplicated informative-index-position test whose two
implementations read different inputs (§10.3), and a stale premise in
`notes/gaps.md` §7 (§10.4).

---

## 1. The two languages

**Source.** CIC terms as the plugin sees them after `Coq_convert`, i.e. the
`coqterm` datatype. Every source type has a **sort**. Write `prop(A)` when
`A`'s sort is `Prop`; call such a type *propositional*, and any other
(`Set`/`Type`-sorted) type *informative*.

**Target.** Untyped first-order logic with equality. One flat domain of terms;
terms are constants, variables, and binary application `f·x`. Formulas are
built from `=`, the constants `$True` and `$False`, the connectives
`¬ ∧ ∨ → ↔`, the quantifiers `∀ ∃`, and one distinguished binary predicate
`$HasType` (`mk_hastype`, `coqterms.ml:134`; with `opt_hastype = false` it
degenerates to applying the type as a unary predicate).

The target domain contains **junk**: elements denoting no well-typed CIC value.
The logic is untyped, so nothing excludes them. Every emitted formula must
therefore be either true of junk as well, or relativized so junk is excluded.
Relativization is what guards do (§3), and every soundness argument in the
translation runs through this *junk model*.

## 2. Erasure

`$Proof` is a distinguished constant. Every term of propositional type
translates to it, and it occupies no argument position:

    ⟦t⟧    = $Proof            if t's type is propositional
    ⟦t u⟧  = ⟦t⟧               if ⟦u⟧ = $Proof
    ⟦t u⟧  = ⟦t⟧ · ⟦u⟧         otherwise

The second line is `convert`'s application case (`coq_transl.ml:2324`,
`if y2 = Const("$Proof") then return x2`). So a constructor `c a p b` with `p` a
proof becomes the binary term `c(a,b)`, not a ternary one.

This is extraction's program/specification split, done literally: the proof is
deleted from the term, and its content is re-attached as a formula, which is
what §3 and §5 do. The pruning is pinned by a golden assertion
(`tests/plugin/check-extraction-transl.sh:132`).

## 3. Two translations of a type

**⟨A⟩ -- a propositional type read as a formula.** Defined when `prop(A)`
(`prop_to_formula`, `coq_transl.ml:2395`):

    ⟨∀(y:B), C⟩  =  ⟨B⟩ → ⟨C⟩                    if prop(B)
    ⟨∀(y:B), C⟩  =  ∀y. G(y,B) → ⟨C⟩             otherwise
    ⟨t = u⟩      =  ⟦t⟧ = ⟦u⟧
    ⟨A ∧ B⟩, ⟨A ∨ B⟩, ⟨¬A⟩  =  the matching connective on the translated parts
    ⟨P t̄⟩        =  ⟦P t̄⟧, read as an atom

**G(x, A) -- the guard.** A formula asserting "the target term `x` inhabits the
source type `A`". This is the relativization that carves the well-typed part
out of the junk domain (`make_guard`, `coq_transl.ml:2588`; `type_to_guard`,
`:2603`; `guard_leaf`, `:2411`):

    G(x, ∀(y:B), C)  =  ⟨B⟩ → G(x, C)            if prop(B)   -- x NOT applied
    G(x, ∀(y:B), C)  =  ∀y. G(y,B) → G(x·y, C)   otherwise
    G(x, A)          =  $HasType(x, ⟦A⟧)         A not a product

The first line is where erasure and guarding meet: a proof argument becomes a
premise and `x` is not applied across it, matching the pruned arity of §2.

Under `opt_type_lifting` (default on) a product is first lifted to a fresh
symbol and its guard becomes an atom again, with a separate unfolding axiom
`∀v. $HasType(v, tp) → G(v, A)`. That axiom is an implication and deliberately
not an equivalence: over an empty domain the equivalence would let a
non-function inhabit an arrow type, and with a functional-extensionality
premise that derives `$false` (`coq_transl.ml:3040`).

Guards are emitted at quantifiers (`∀(x:A). φ` becomes `∀x. G(x,A) → φ`;
`∃(x:A). φ` becomes `∃x. G(x,A) ∧ φ`, `coq_transl.ml:2145`), on the free
variables of an axiom when closing it (`mk_guards`, `:830`), and as the whole
content of a constant's typing axiom (`add_typing_axiom`, `:3073`).

## 4. An inductive declaration

Fix an inductive

    I : ∀ (p₁:P₁)…(p_m:P_m) (i₁:J₁)…(i_n:J_n). s

The `p̄` are **parameters**, fixed across all constructors; the `ī` are
**indices**, which may vary per constructor. Each constructor has the form

    c : ∀ (p̄ : P̄) (a₁:A₁)…(a_k:A_k). I p̄ t₁ᶜ … t_nᶜ

where the `t_rᶜ` are `c`'s **result index patterns**. Partition the `aⱼ` into

  * **propositional fields**, those with `prop(Aⱼ)` -- these are the
    specification;
  * **informative fields**, the rest -- these are the data.

An index position `r` is **informative** when `prop(J_r)` is false;
propositional index positions are ignored throughout, since both sides of any
equation about them would be `$Proof`.

**Fording** (`ford_indices`, `coq_erasure.ml`). For a constructor `c`, walk the
informative index positions left to right. If `t_rᶜ` is exactly one of `c`'s
own informative fields `aⱼ`, and no earlier position already claimed `aⱼ`, then
`aⱼ` is **solved** by position `r`: it is not quantified over, and every
occurrence of it is replaced by the index `i_r`. Every remaining informative
position `r` contributes a **residual equation** `i_r = ⟦t_rᶜ⟧`.

The informative fields that are neither propositional nor solved are the
**residual informative fields**, written `inf(c)`. These are exactly the
arguments that survive into the target term `c(p̄, inf(c))`.

## 5. What is emitted for the declaration

Four axiom families, all in `add_def_axioms` (`coq_transl.ml:3419`). A
constructor enters `Defhash` as `(cname, Const cname, ty, sort)`
(`coq_convert.ml:266`), so it contributes only its typing axiom --
`add_def_eq_axiom` returns immediately on `Const(c) when c = name`
(`coq_transl.ml:3186`).

**(a) Constructor typing**, one per constructor: this is just `G` applied to
`c`'s own type, unfolded by the rules of §3.

    ∀ p̄ inf(c).  ⋀ⱼ G(aⱼ, Aⱼ)                    [informative fields]
               →  ⋀ⱼ ⟨Aⱼ⟩                        [propositional fields]
               →  $HasType( c(p̄, inf(c)), I(p̄, ⟦t̄ᶜ⟧) )

The **introduction** direction: to build a value you must discharge the
specification.

**(b) Injectivity**, one per constructor (`add_injection_axioms`, `:3225`):

    ∀ x̄ ȳ.  c(x̄) = c(ȳ)  →  ⋀ { xⱼ = yⱼ : aⱼ informative and not a parameter }

Parameters contribute nothing -- they are fixed by a homogeneous equality and
are not injective payloads, and a parameter-dependent declaration may collapse
constructor instances elsewhere, so inferring parameter equality from the
erased premise would be unsound. Propositional fields contribute nothing
either: by proof irrelevance any two proofs of one proposition are
interchangeable. They are replaced by a neutral marker rather than by a
`$Proof = $Proof` tautology (`:3240`), pinned by a `forbid_pattern`
(`check-extraction-transl.sh:105`).

**(c) Discrimination**, one per unordered pair of distinct constructors
(`add_discrim_axioms`, `:3317`):

    ∀ x̄ ȳ.  c(x̄) ≠ c′(ȳ)

**(d) Inversion**, one per inductive (`add_inversion_axioms`, `:3380`;
`mk_inversion`, `:754`; index equations from `mk_inversion_conjs`, `:730`,
under `opt_precise_inversion`, default on):

    ∀ p̄ ī w.  $HasType(w, I(p̄,ī))  →
        ⋁_c  ∃ inf(c).  ⋀ { i_r = ⟦t_rᶜ⟧ : r an informative index position }
                      ∧ ⋀ { ⟨Aⱼ⟩ : aⱼ a propositional field }
                      ∧ w = c(p̄, inf(c))

The **elimination** direction. The propositional fields appear as conjuncts
because `convert`'s `Quant` case turns an existential over a propositional
binder into a conjunction, substituting `$Proof` for the binder in the body
(`:2295`); the constructor spine then drops that `$Proof` by §2, so (a) and (d)
agree on arity.

Nothing propositional is lost across (a)-(d). Both directions are conditioned
on premise selection having retained every constructor: `add_inversion_axioms`
and `add_injection_axioms` both bail out otherwise (`:3382`, `:3227`).

## 6. What is emitted at an occurrence

Wherever the translation needs "`w` inhabits `I p̄ ū`" it emits `G(w, I p̄ ū)`.
In general this is the opaque atom

    G(w, I p̄ ū)  =  $HasType(w, I(p̄, ū))

`guard_leaf`'s `classify_leaf` returns `None` for the general case and falls
through to `fallback ()` (`coq_transl.ml:2495`, `:2413`).

Two shapes are expanded instead. They are exactly the cases in which the body
of axiom (d) simplifies enough to be inlined:

**Every constructor has `inf(c) = ∅`** (`CEnum`). The existential binds
nothing, so the disjunction is quantifier-free and ground:

    G(w, I p̄ ū)  =  ⋁_c ( w = c(p̄) ∧ ⋀ ⟨Aⱼ⟩ ∧ ⋀ i_r = ⟦t_rᶜ⟧ [ū/ī] )

**One constructor; `inf(c)` a single field `a`; at least one propositional
field; and `a`'s type does not reach `I` through any constructor telescope**
(`CSubset`; the last condition is `carrier_reaches_inductive`,
`coq_erasure.ml:460`, transitive through the inductive dependency graph). Then
the equation `w = c(a)` orients as `a := w`, deleting both the quantifier and
the constructor symbol -- `w` *is* the field:

    G(w, {a : A | P a})  =  G(w, A) ∧ ⟨P w⟩

Because the constructor symbol then denotes nothing, axioms (a), (b) and (d)
are suppressed for such a declaration (`skip_refinement_decl_axioms`,
`coq_transl.ml:3219`).

The non-reachability condition is load-bearing twice: it is Letouzey's
non-recursive-carrier condition for extraction soundness, *and* it is what makes
the recursive call `G(w, A)` in the expansion terminate. §9.2 returns to this.

## 7. What is emitted for a match

A `match` is lifted to a fresh function symbol `f` applied to the free
variables in scope, and defined by one equation per constructor:

    ∀ (vars before) inf(c) (vars after).
        f( …, c(p̄, inf(c)), … )  =  ⟦ branch_c [ propositional fields := $Proof ] ⟧

(`prepare_case_branch` and the fold at `coq_transl.ml:2075`; the substitution is
`subst_proof_args`, `:1475`.) A branch is omitted when some informative index
position has actual and pattern rigidly incompatible -- distinct constructors at
the head -- since no value of `I p̄ ū` can arise from that constructor
(`branch_clashes`/`rigid_clash`, `:2038`, `:927`).

These equations carry no guard: they hold of junk arguments too. That is sound
because `f` is a fresh total function symbol whose value on junk is otherwise
unconstrained, and because no *value* can depend on an erased proof -- the
branch body erased it as well. What is lost is that the branch equation carries
no specification: `P x` is recoverable only through (d) applied to the
scrutinee.

---

## 8. The gap

Compare the two forms available for a hypothesis `h`:

    general:   $HasType(h, I(p̄,ū))
    CSubset:   G(h, A) ∧ ⟨P h⟩

Both assert the same thing. The second states the specification **as a formula
about `h` itself**, immediately available. The first states it nowhere; to
obtain `P` a prover must resolve `$HasType(h, I(p̄,ū))` against the antecedent
of the generic axiom (d), instantiating `p̄`, `ī`, `w`, and then reason about
the Skolem terms of its existential -- which, because that existential lies
under the axiom's universals, are Skolem *functions* rather than constants.

This is the whole gap, and it is a matter of prover search, not of missing
content. The specification is present (§5); it is behind an instantiation step.

Note that the earlier framing "per-occurrence expansion is clause-for-clause
the same as the instantiated inversion axiom" is **wrong**, and the reason
matters for the design. A local hypothesis reaches the translation as a
constant with an *asserted* typing axiom `$_typeof_h : G(h, I p̄ ū)`. Asserted
means positive: expanding it there puts `⋁_c ∃ inf(c). …` in a positive
position with no enclosing universals, so clausification Skolemizes the
existentials into **constants** and the disjunction becomes ground facts. That
is strictly cheaper than instantiating (d) and working under Skolem functions.
Per-occurrence expansion buys something real, with no new symbols.

## 9. How the translation should support this in general

### 9.1 One rule

Replace the two special cases and the opaque fallback by a single expansion,
which is `notes/indexed_families.md` §2.3's schema with the informative fields'
own guards made explicit:

    G(w, I p̄ ū)  =  ⋁_c ∃ inf(c).  w = c(p̄, inf(c))
                                 ∧ ⋀ⱼ G(aⱼ, Aⱼ)      [informative fields]
                                 ∧ ⋀ⱼ ⟨Aⱼ⟩           [propositional fields]
                                 ∧ ⋀_r i_r = ⟦t_rᶜ⟧ [ū/ī]

Both current shapes are simplifications of this, not separate concepts:

  * `inf(c) = ∅` for every `c` ⟹ the existential binds nothing, and the rule
    reduces to today's `CEnum` expansion;
  * one constructor with `inf(c) = {a}` ⟹ the equation `w = c(a)` orients as
    `a := w`, deleting the quantifier and the constructor symbol, and the rule
    reduces to today's `CSubset` expansion.

Consequently `ind_class` should **shrink**, not grow: `CEnum` and `CSubset`
stop being classifications and become rewrite rules applied to one formula.
`CEmpty` is the further degenerate case of an empty disjunction (`$False`), and
`CPropSingleton` remains what it is -- a statement about match collapse, not
about guards. This is the "no options for dominated variants" discipline
applied to the classifier itself: one mechanism with simplification rules,
rather than three shapes with three code paths.

### 9.2 The condition that makes it well-defined: termination

The rule recurses through `G(aⱼ, Aⱼ)`. For a recursive family some `Aⱼ` *is*
the family, and the expansion does not terminate.

Today this cannot happen, but only structurally, and by accident of the two
shapes' side conditions: `CSubset` requires the carrier not to reach the
inductive (`carrier_reaches_inductive`), and `CEnum` has no informative fields
to recurse on at all. **There is no expansion-depth guard anywhere in the
plugin** -- the only budget is `opt_whnf_budget = 64`, which bounds head
normalization when exposing a scrutinee's inductive type and is unrelated
(verified by grep over `coq_transl.ml` and `coq_transl_opts.ml`). Generalizing
the rule therefore *requires* introducing one, and the right one is structural
rather than a fuel counter:

> At a field whose type reaches `I` through any constructor telescope, stop and
> emit `$HasType(aⱼ, I(…))` instead of expanding.

`carrier_reaches_inductive` already computes exactly this predicate, already
transitively through the inductive dependency graph, already with a visited set
so that ordinary recursive types such as `nat` terminate rather than being
mistaken for a cycle. It needs no change, only a second caller.

The consequence is worth stating plainly, because it bounds what
"specification extraction" can mean here: the expansion is **one constructor
layer deep**. You obtain the head constructor's specification and index
constraints, not the whole structure's invariant. For propositional payloads
this is almost always the whole story, since a payload's type rarely recurses
into the family; for informative fields it is the correct fixpoint rather than
a restriction -- deeper structure remains reachable, one layer at a time,
through (d).

### 9.3 What is probably not needed: selectors

An earlier version of this proposal assumed the general case needs projection
symbols `π_cⁱ` with defining equations `π_cⁱ(c(x̄)) = xᵢ`, on the grounds that
only a quantifier-free guard is usable in both polarities. That is the
SMT-datatype and F* projector encoding, and it would make `CSubset` literally
the identity-projection case -- elegant, but it introduces new symbols with
bridge axioms, against the shallow-translation policy.

On reflection it is probably unnecessary, for a reason that also sharpens what
the feature is:

**Specification extraction is a positive-position phenomenon.** A guard in
negative position (`∀x. G(x,A) → φ(x)`, the shape of every premise about a
bound variable) is an *obligation*: to use the premise you must prove
membership, and the specification is what you must supply, not what you
receive. That direction is already served by axiom (a). A guard in positive
position -- an asserted `$_typeof_` axiom, which is how hypotheses and
constants arrive -- is where a specification is *received*, and there the
existential Skolemizes to constants (or, under enclosing universals, to
functions of those universals, which is still no worse than (d)).

So selectors buy only term sharing: one selector symbol where clausification
would otherwise mint several Skolem symbols. That is a clause-shape
optimization to be justified by measurement, not a prerequisite. Stage 3 at
most; possibly never.

### 9.4 Cost

The expanded guard is `n` constructors wide, each carrying its informative
fields' guards, its payloads and its index equations. Inlined at every
occurrence, this is a clause-size multiplier, and clause size is the currency
in which recent regressions were paid (`notes/gaps.md` §7 records the
refinement-expansion stdlib episode, 693→729 KB, tipping threshold-noisy
cells). Two mitigations are available and should be part of the first
implementation rather than a follow-up:

  * expand only where there is something to extract -- at least one
    propositional field, or at least one residual index equation. A family with
    neither has an expansion that says no more than `$HasType` plus the
    inversion axiom already do, and should keep the atom.
  * once a family is expanded at every occurrence, its declaration-level (b)
    and (d) become largely redundant; `skip_refinement_decl_axioms` generalizes
    to it. This is `notes/indexed_families.md`'s Phase D, and it is what keeps
    the net clause-size change from being a pure addition. Measure before
    enabling: (d) is still needed for occurrences the expansion declines
    (§9.2's recursive stop, and partial applications).

## 10. Obligations and open items

### 10.1 Positive-position domain closure

`notes/indexed_families.md` §2.3 already flags this and it becomes
load-bearing under §9.1, since the disjunction would appear at far more
occurrences. The disjunction asserts exhaustiveness *relative to the guard*.
Unguarded, that is domain closure -- Meng-Paulson's cardinality bomb, false in
the junk model. The expansion is per-occurrence and always sits at a guard
position, so this holds by construction; but it is the invariant the
consistency canaries must pin, and it should be stated as a model obligation
in the soundness paper before the option goes default-on.

### 10.2 Reconstruction

Every occurrence expanded is an occurrence whose ATP proof mentions
constructors and payloads rather than an opaque typing atom. `sauto`-based
reconstruction handles this for `CSubset`/`CEnum` today; whether it does for
wide multi-constructor disjunctions is unmeasured and is the usual silent
killer. The eval harness measures end-to-end, which is the right metric.

### 10.3 Defect: two implementations of "informative index position"

Independent of this proposal. The predicate is computed twice, from different
inputs:

  * `Coq_erasure.informative_index_mask` (`coq_erasure.ml:192`) -- `check_prop`
    on index formals **instantiated at the occurrence's parameters**
    (`index_formals_of … params`), in the caller's local context
    (`List.rev vars` at `coq_transl.ml:1998`). Used by fording and by the
    case path's branch pruning.
  * `mk_inversion_conjs` (`coq_transl.ml:730`) -- the same `check_prop`
    predicate on the **uninstantiated declared telescope**
    (`get_type_args indtype`, parameters left as universally quantified
    variables), from a context holding only the parameter formals. Used by
    axiom (d).

For a parameter-dependent index type these can disagree: axiom (d) quantifies
over parameters that a given occurrence may instantiate with a `Prop`. This is
exactly the "guard and case must ford the same positions" hazard that
`ford_indices`'s own doc comment warns about, extended to the third consumer,
where nothing currently enforces agreement. It matters more under §9.1, since
guard and inversion would then overlap on most families rather than a handful.
Whether they diverge on real code is unverified; `check_prop`'s incompleteness
means it cannot be settled by reading. Fix: have `mk_inversion_conjs` call
`informative_index_mask`.

### 10.4 Defect: stale premise in `notes/gaps.md` §7

That section states that "a function with a proof argument is translated at
full arity with `$Proof` filling the slot … the translation currently only
canonicalizes them", and prices Letouzey-style signature pruning as cheap and
early partly on that basis. For **proof** arguments this is not what the code
does: `convert` drops them from spines (`coq_transl.ml:2324`) and
`type_to_guard` prunes the domain without applying the subject
(`coq_transl.ml:2603`), with a golden test pinning it
(`check-extraction-transl.sh:132`). The **type**-argument half of §7 (dead
ground type arguments after monomorphisation) stands. §7's motivation should be
restated on that half alone.

## 11. Staging

  * **Stage 1 -- non-recursive families, all constructor counts.** Drop
    `classify_leaf`'s filter (`coq_transl.ml:2495`) and apply §9.1 to any
    saturated occurrence whose informative fields do not reach the family and
    which has at least one propositional field or residual index equation.
    Reuses `carrier_reaches_inductive`, `ford_indices`,
    `informative_index_mask` and the existing `prepare_telescope`/
    `index_equations` machinery unchanged. This closes the "why only one
    constructor, why only one carrier" question: multi-constructor records,
    `Compare`-style types, indexed enums carrying data.
  * **Stage 2 -- recursive families.** One-layer expansion with the §9.2 stop
    rule.
  * **Stage 3 -- selectors.** Only if measurement shows Skolem-symbol
    proliferation is costing more than the sharing would save. §9.3 expects it
    will not.

Per the standing methodology: a compile-time `opt_*` flag wired into
`eval/rebuild-config.sh`, its own leave-one-out screening axis, golden
assertions in `tests/plugin/check-extraction-transl.sh` for the new guard
shape, and a `check-consistency.sh` canary extension over dumps exercising it
-- the invariant to pin being §10.1.

## 12. Verification status

§§1-7 were read out of the sources named in the dateline; every file and line
reference in them was checked against the code while writing. Specific
behaviours confirmed by reading: proof-argument pruning in spines and in
`type_to_guard`; the constructor `Defhash` shape and the resulting single
typing axiom; the proof-irrelevance marker in injectivity; the propositional
conjuncts in inversion; the absence of any expansion-depth guard (§9.2). Two
behaviours were confirmed indirectly through the golden assertions in
`tests/plugin/check-extraction-transl.sh` rather than by inspecting output.

Nothing was verified empirically: no build was run, no problem was translated,
no TPTP dump was inspected for this note. The clause-size argument in §9.4 is
carried over from `notes/gaps.md`, not measured here. §10.3's divergence is
argued from the code and not exhibited on an actual declaration. The claim in
§9.3 that selectors are unnecessary is an argument about polarity, not a
measurement, and is the part of this note most likely to be wrong.
