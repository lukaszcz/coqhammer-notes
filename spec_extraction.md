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
Nothing here was verified by running the translation; see §12.
Updated 2026-11-20: §5(a)/(d) corrected against `Hammer_transl` output, and
§9.5 (index unification at occurrences) and §9.6 (rejected alternatives)
added.*

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
7. Fording and rigid-clash pruning should become one procedure: first-order
   unification of a constructor's result-index patterns against the
   occurrence's actual indices, with outcomes *solved*, *clash* and *stuck*.
   On the guard side it removes impossible disjuncts and solved existentials,
   which shrinks exactly the clauses §9.4 worries about; it introduces no
   symbols. §9.5. Encodings that would generalize further but break
   shallowness are recorded as rejected in §9.6.

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

Fording is an occurrence-level operation: it needs actual indices to solve
fields with. The declaration-level axioms below see only the index formals, so
they quantify over **all** informative fields of `c`, solved or not. Write
`inf₀(c)` for that list; `inf(c) ⊆ inf₀(c)` is what remains after fording at a
particular occurrence.

**(a) Constructor typing**, one per constructor: this is just `G` applied to
`c`'s own type, unfolded by the rules of §3.

    ∀ p̄ inf₀(c).  ⋀ⱼ G(aⱼ, Aⱼ)                   [informative fields]
                →  ⋀ⱼ ⟨Aⱼ⟩                       [propositional fields]
                →  $HasType( c(p̄, inf₀(c)), I(p̄, ⟦t̄ᶜ⟧) )

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
        ⋁_c  ∃ inf₀(c).  ⋀ { G(aⱼ, Aⱼ) : aⱼ an informative field }
                       ∧ ⋀ { ⟨Aⱼ⟩ : aⱼ a propositional field }
                       ∧ ⋀ { i_r = ⟦t_rᶜ⟧ : r an informative index position }
                       ∧ w = c(p̄, inf₀(c))

The **elimination** direction. Both kinds of field appear as conjuncts through
`convert`'s `Quant` case (`:2145`): an existential over an informative binder
becomes `∃aⱼ. G(aⱼ, Aⱼ) ∧ …`, and one over a propositional binder becomes a
conjunction with `⟨Aⱼ⟩`, substituting `$Proof` for the binder in the body; the
constructor spine then drops that `$Proof` by §2, so (a) and (d) agree on
arity. A field that fording would solve at an occurrence is still quantified
here, with the index equation `i_r = a_j` among the conjuncts.

*Checked with `Hammer_transl` (2026-11-20).* For
`tag : ∀ n : nat, bool → n < 5 → tagged n` the axiom is

    ∀i X. nat(i) → HasType(X, tagged(i)) →
        ∃n. nat(n) ∧ ∃b. (b = true ∨ b = false) ∧ n < 5 ∧ i = n ∧ X = tag(n, b)

with the `bool` field's guard already expanded by the `CEnum` rule of §6. For
`vcons : A → ∀ n, vec A n → vec A (S n)` the `vcons` disjunct carries
`HasType(h, A)`, `nat(n)`, `HasType(t, vec(A, n))` and `i = S n`.

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
own guards made explicit. It is the body of axiom (d) instantiated at the
occurrence (`ī := ū`) and forded there, so that only `inf(c)` remains
quantified -- no content beyond what (d) already states, only a cheaper place
to state it (§8):

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

A third mitigation, index unification, removes disjuncts and quantifiers
outright and is independent of the other two; §9.5.

### 9.5 Index unification at occurrences

Two rules currently read a constructor's result-index patterns `t̄ᶜ` against an
occurrence's actual indices `ū`:

  * **fording** (`ford_indices`, `coq_erasure.ml:239`) solves a field only when
    `t_rᶜ` is *literally* that field;
  * **rigid-clash pruning** (`rigid_clash`, `coq_transl.ml:927`) drops a case
    branch when `u_r` and `t_rᶜ` have distinct constructor heads somewhere
    along a spine of equal heads.

Both are fragments of one procedure: first-order unification of the equations
`{ u_r ≐ t_rᶜ : r informative }`. The unknowns are `c`'s informative fields;
the occurrence side `ū` contains none of them, since it is rigid in the
caller's context. The rules, applied to a selected equation `u ≐ t`:

  * **delete** -- `u` and `t` syntactically equal: drop the equation.
  * **solve** -- `t` is an unknown `aⱼ` not yet solved: record `aⱼ := u` and
    substitute it into the remaining equations, the field types and the
    payloads. `u` contains no unknowns, so there is no occurs check. This is
    today's fording rule, unchanged.
  * **decompose** -- both sides have the same constructor head `d`: replace the
    equation by one equation per argument position of `d` that survives
    erasure and is not a parameter of `d`'s inductive. These are exactly the
    positions axiom (b) relates.
  * **clash** -- distinct constructor heads: the constructor `c` cannot produce
    a value of `I p̄ ū`.
  * **stuck** -- anything else (a variable or a non-constructor head on the
    occurrence side, against a pattern that is not an unknown): keep `u = t`,
    under the substitution so far, as a residual index equation.

A field that occurs twice in `t̄ᶜ` is solved at its first occurrence; the
second then yields an equation between two occurrence-side terms, which the
same rules delete, prune or keep. The occurrence side is head-normalized with
`budgeted_whnf` (`coq_erasure.ml:287`), as `rigid_clash` does today. A head the
budget does not expose is not a constructor, so the equation is stuck, which
is always the safe outcome.

**Every rule must be an equivalence in the junk model, not an implication.**
A guard occurs in both polarities (§9.3), so a rule that merely weakened it
would make a premise-position guard, and hence the axiom containing it, too
strong. Delete and solve are equivalences outright, because they substitute
an equal term. Clash holds by discrimination (c), and decompose by injectivity
(b), restricted to the positions (b) states: parameters and proof positions
are never decomposed. A collapsed `CSubset` constructor has no symbol left in
the output and so is not a rigid head; it neither clashes nor decomposes. This
is the soundness condition. It also keeps the rules aligned with axioms (b)
and (c), which a prover would otherwise use to derive the same consequences
at search time.

**Guard side** (§9.1, and today's `CEnum`/`CSubset` expansion). For each
constructor:

  * *clash* drops the disjunct. `guard_leaf` (`coq_transl.ml:2411`) prunes
    nothing today. An `ev 3` hypothesis expanded under §9.1 would keep
    disjuncts with `3 = 0` and `3 = S (S n)` conjuncts, for the prover to
    refute with (c) and (b) at every use.
  * *solve* removes the field's existential and substitutes `u` for it. With
    occurrence index `S k` against pattern `S n`, decompose and solve give
    `n := k`, where today the guard keeps `∃n. S k = S n ∧ …`.
  * *stuck* equations are the residual index equations, as now.

Unification therefore shrinks exactly the clauses §9.4 prices, most strongly
at the ground and constructor-headed indices that are common in hypotheses.
It adds no symbol and no axiom.

**Case side.** Clash is today's branch pruning. A clash found only after a
solve -- a non-linear pattern, or a solved field occurring in a later index --
extends it. Solutions beyond today's bare-variable fording need *not* be
applied to branch equations. A branch equation quantified over a field is
valid for junk too (§7), and strictly more general than its instance at the
solution. Instantiating is required only where the field leaves the
constructor term, i.e. for `CSubset` carrier collapse, and there fording
already applies.

**Declaration side.** With formal indices every equation is stuck or a
bare-variable solve against a formal. Today (d) leaves even the latter as
`∃aⱼ. … ∧ i_r = aⱼ` (the `tagged` example of §5). Adopting the solve there is
an equivalent simplification, to be measured like any other clause-shape
change. Whether or not it is adopted, (d) should compute its informative mask
through the same procedure, which closes §10.3.

**Implementation.** One function in `Coq_erasure` returning
`Solved σ | Clash | Stuck of residual equations`, called by the
classification, by `guard_leaf`, by `prepare_case_branch`/`branch_clashes`
and by `mk_inversion_conjs`. `ford_indices` and `rigid_clash` become its
special cases. The guard and case paths must agree on solved positions, the
hazard `ford_indices`' doc comment describes; with one implementation this
holds structurally.

### 9.6 Rejected alternatives

Encodings that would generalize further, each recorded with the reason it
breaks the shallow-translation policy (`notes/dependent_types.md` §4,
principle 4; `notes/extraction/sections/shallow.tex`, S2-S4), so that they are
not proposed again:

  * **A named inhabitation predicate per family**, `T_I(p̄, ī, x)`, defined by
    introduction and complete-inversion axioms, with per-occurrence inlining
    kept as an optional heuristic. This is the `HasType`-plus-unfolding
    encoding: the specification would sit behind an instantiation step at
    every use. §9.1 states the same content at the occurrence.
  * **Accessor symbols for forced fields** (Brady-style forcing with
    `n := pred(ī)`). This adds new symbols with defining equations the prover
    must rewrite with, i.e. the selector encoding of §9.3. §9.5 recovers the
    constructor-headed case with no new symbols. When the index is a variable,
    the field simply stays existential.
  * **Uniform constructor arity with `$Proof` placeholders**, to make
    informativeness masks independent of parameter instantiation. This
    contradicts S4 (proofs never become terms) and the pruning golden test
    (`check-extraction-transl.sh:132`). The mask disagreement it would address
    is §10.3, whose local fix is simpler.
  * **Type-level functions as predicate definitions** (`T_F(c(…), x) ↔
    G(x, branch type)`). This makes each type-level function an inhabitation
    predicate with unfolding axioms, the same objection as the first bullet.
    Type-level computation stays with translation-time head normalization
    under `opt_whnf_budget`.

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
  * **Independent of Stages 1-3 -- index unification (§9.5).** First as a
    behaviour-preserving refactor: `ford_indices` and `rigid_clash` re-expressed
    through the one procedure, and `mk_inversion_conjs` reading its mask (§10.3).
    The golden assertions must be unchanged, and that is the check. Then guard-side
    clash and solve on today's `CEnum`/`CSubset` guards, measurable before
    Stage 1, and carried into Stages 1-2 as part of the expansion.

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

*2026-11-20.* The one empirical check so far is `Hammer_transl` on three small
declarations: `tagged`, `vec`, and a single-constructor type with two `nat`
fields and an `n < m` proof field. It confirmed the shape of axiom (d) now
given in §5. Data fields carry their guards, proof fields their propositions,
and solvable fields stay quantified with an index equation. That corrected the
earlier statement of (d), which listed neither the field guards nor the
unforded quantification.

Caveat on provenance: the plugin that ran was the one installed in the default
opam switch on 2026-08-08, i.e. from the #231 merge (`6029473`), not from
`rocq-9.2` HEAD. The code that produces (d) is textually identical between the
two: `mk_inversion_conjs`/`mk_inversion`/`mk_prop_inversion`,
`add_inversion_axioms0`, `add_inversion_axioms`, and `convert`'s `Quant` case,
diffed `6029473..27b80e8`. The `bool` field's expanded guard comes from
`guard_leaf`, which #234 did change, so that detail of the `tagged` output
should be re-checked on HEAD.

§9.5's claims -- that `guard_leaf` prunes no clashing disjunct, and the
model-equivalence of its rules -- are argued from the code and from (b)/(c),
not exhibited.
