# Specification extraction for dependent inductive types

*Design note, 2026-08-31. Written as the question left open by
`notes/indexed_families.md` §2.3 and `notes/gaps.md`: the translation expands
refinements and enums (`CSubset`, `CEnum`) into formulas a prover can use
directly, maps empty guards to false, and uses a membership atom for regular
data families. What does the general case actually get, and what would it take to make the specification of an arbitrary dependent
inductive ATP-usable? §§1-7 below are a self-contained description of what the
code does today, written so that the proposal in §§8-11 has no undefined terms.
Sources, all read for this note: `src/plugin/coq_transl.ml`,
`src/plugin/coq_erasure.ml`/`.mli`, `src/plugin/coq_convert.ml`,
`src/plugin/coqterms.ml`, `src/plugin/coq_transl_opts.ml`,
`tests/plugin/check-extraction-transl.sh` (branch `fording`, Rocq 9.2).
Sibling notes: `notes/dependent_types.md`, `notes/extraction.md`,
`notes/indexed_families.md`, `notes/type_guards.md`, `notes/gaps.md`.
Updated 2026-11-20 against the Rocq 9.2 worktree at `27b80e8`. §§8–11 specify
how to share inversion in the emitted ATP problem. §12 gives the scope of the
measurements.* [Adversarial review and probe details](reviews/spec-extraction-adversarial-review.md)

## TL;DR

1. For a regular data family, use the existing membership atom at each guard
   and emit the complete, guarded inversion axiom once per family per selected
   problem. The axiom binds each constructor's data fields together with
   their types, index equations and dependent proof payloads (§§5, 8).
2. Specialize where the indices or the goal give a concrete saving. An
   index-only fact can be stated directly. A payload `P(x,y)` about hidden
   data needs the same witnesses that construct the inhabitant (§9.1).
3. A single small local consequence can be worthwhile. When the same
   specialization is useful at several guards, keep their membership atoms
   and share one quantified rule for that index shape. Wide or unreduced
   cases use the generic axiom. This policy introduces no new membership
   predicate or selector (§§9.3–9.4).
4. Specialization preserves the constructor's erased representation, and
   checked index matching retains every unsolved equation. Bound expansion
   through proof payloads as well as data fields (§§9.2, 9.5).
5. Test the size of the printed and clausified problems, ATP success, and
   reconstruction with the originating local hypothesis available (§§10–12).

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
**residual informative fields**, written `inf(c)`. These fields still need
witnesses. A solved data field stays in its original slot in a represented
constructor's term, filled by its solution. Proof erasure and the separate
`CSubset` carrier representation (§6) determine the target spine.

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

**(a) Constructor typing** applies `G` to `c`'s own type. The schema below
shows its unfolded form for a regular data family, with parameters assumed
well typed.

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

    ∀ p̄ ī w.  D(p̄,ī) ∧ $HasType(w, I(p̄,ī))  →
        ⋁_c  ∃ inf₀(c).  ⋀ { G(aⱼ, Aⱼ) : aⱼ an informative field }
                       ∧ ⋀ { ⟨Aⱼ⟩ : aⱼ a propositional field }
                       ∧ ⋀ { i_r = ⟦t_rᶜ⟧ : r an informative index position }
                       ∧ w = c(p̄, inf₀(c))

Here `D(p̄,ī)` abbreviates the applicable guards on parameters and indices.
This is the **elimination** direction. Both kinds of field appear as conjuncts through
`convert`'s `Quant` case (`:2145`): an existential over an informative binder
becomes `∃aⱼ. G(aⱼ, Aⱼ) ∧ …`, and one over a propositional binder becomes a
conjunction with `⟨Aⱼ⟩`, substituting `$Proof` for the binder in the body; the
constructor spine then drops that `$Proof` by §2, so (a) and (d) agree on
arity. A field that fording would solve at an occurrence is still quantified
here, with the index equation `i_r = a_j` among the conjuncts.

For a regular example on `27b80e8`, take
`pack : ∀ n, nat → nat → P n → packet n`. The dumped inversion is, with
grouped quantifiers and abbreviated names,

    ∀ i h. Nat(i) → M(h,i) →
      ∃ n x y. Nat(n) ∧ Nat(x) ∧ Nat(y) ∧ P(n) ∧ i=n ∧ h=pack(n,x,y).

Here `M(h,i)` abbreviates the existing membership of `packet i`. Substituting
`n := i` simplifies the shared axiom itself. In contrast, the earlier probe
`tag : ∀ n, bool → n < 5 → tagged n` is already a subset on this revision.
Its guard for `h : tagged 3` is `(h=true ∨ h=false) ∧ 3<5` up to trivial
conjuncts. It has no declaration-level inversion axiom.

Exhaustiveness requires every constructor telescope. If one is unavailable,
omit the inverse and any specialization requiring that exhaustive analysis.
Typing and injection depend on the individual constructor, and discrimination
depends on the pair.

## 6. What is emitted at an occurrence

Wherever the translation needs "`w` inhabits `I p̄ ū`" it emits `G(w, I p̄ ū)`.
In general this is the opaque atom

    G(w, I p̄ ū)  =  $HasType(w, I(p̄, ū))

`guard_leaf`'s `classify_leaf` returns `None` for the general case and falls
through to `fallback ()` (`coq_transl.ml:2495`, `:2413`).

Three cases admit a direct guard. An empty data type has guard `$False`.
For a `CEnum`, every constructor has `inf(c) = ∅`. The guard is a
disjunction of tag equalities, translated payloads and residual index
equations. The tag contains the solved data arguments at their occurrence
values. The outer constructor case introduces no existential data binders,
although a payload can contain its own quantifiers.

A validated `CSubset` has one constructor, one residual carrier and at least
one proof field. Constructor conversion represents the value by its carrier.
For the ordinary subset this gives

    G(w, {a : A | P a}) = G(w, A) ∧ ⟨P w⟩.

This equality relies on that representation choice in term and match
translation. An ordinary constructor equation `w = c(a)` alone does not
license `a := w`. The classifier checks carrier reachability and dependencies
among fields. For declaration-independent collapse,
`skip_refinement_decl_axioms` skips injection and inversion. Constructor
typing has its own path. The carrier check covers only part of the recursion
involved in expanding a guard (§9.2).

## 7. What is emitted for a match

On the ordinary data-returning split-equation path, a `match` is lifted to
a fresh function symbol `f` applied to the free variables in scope. Each
surviving constructor contributes an equation of the form below.

    ∀ (vars before) inf(c) (vars after).
        f( …, ⟦c p̄ āσ⟧, … )  =  ⟦ branch_c[σ] ⟧

Here `σ` fills solved slots with the occurrence indices and erases proof
arguments, using the same spine on both sides
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

## 8. What gets duplicated

For a regular family `I`, write `M(h,i)` for the existing membership atom
and `E(h,i)` for the disjunction in §5(d), specialized at `i`. Both are
notation in this note. For example, with one constructor and a proof payload
depending on both fields, its case might be

    E(h,i) ≡ ∃ x y. G(x,A) ∧ G(y,B(x)) ∧ i=f(x,y) ∧ h=c(x,y) ∧ P(x,y).

Suppose two hypotheses inhabit the same fiber. Inlining writes `E(h₁,i)` and
`E(h₂,i)`. Each copy contains the entire telescope, constructor equality and
payload. With eight viable constructors it writes the eight-way choice twice.
An *occurrence* here is a request to generate a type guard, for example the
typing of a local hypothesis or the domain of a quantified lemma. Simply
using the term `h₁` twice in a goal does not request two guards.

Write `D` for the index guard and suppress the family parameters. The shared
encoding of this context has three ground facts and one quantified axiom.

    D(i)
    M(h₁,i)
    M(h₂,i)
    ∀ j w. D(j) ∧ M(w,j) → E(w,j).

Emit the last formula once. The ATP can instantiate it at either inhabitant.
Each instantiation has its own witnesses, and all occurrences of `x,y` *within*
a constructor case refer to the same pair. Sharing witnesses across distinct
inhabitants would incorrectly identify their fields. The input contains a single constructor analysis, which the prover can
clausify once. Search may still instantiate the rule many times.

## 9. How to specialize shared inversion

### 9.1 The full dependent specification

For a saturated occurrence, match each constructor's result indices against
the actual indices (§9.5). For each viable constructor `c`, let `σ` contain
the solved fields and proof erasures, and bind the residual informative fields
in telescope order. Its branch is the conjunction of

* the equality of `w` with the translated **full** constructor spine under `σ`,
* each informative field's guard at its instantiated, possibly dependent type,
* each translated proof payload under the same substitution and binders, and
* the residual index equations.

Existentially close each branch and disjoin the branches. This gives the
specialized body of inversion. In §8, the guard for `y` depends on `x`, and
the index, constructor and `P(x,y)` must all refer to those same witnesses.
Separate claims that some pair satisfies `P` and some pair constructs `h`
would lose the correlation needed to prove `P(left(h),right(h))`.

A consequence mentioning only the indices is a useful special case. In the
`packet` example, matching gives `P(i)` directly. If different viable
branches give `L(i)` and `R(i)`, their common consequence is the disjunction
`L(i) ∨ R(i)`. A fact asserted on its own must follow in every viable case.
With existing source projections that compute on the constructor, a
field-dependent consequence may also have a short form about `h`. Otherwise
the existential specification is available through the shared rule. Each
shortcut supplements membership and retains the premises under which it holds.

### 9.2 Bound the work of building a specialization

Use the atomic membership for regular data fields at the next constructor
layer. A recursive tail `t : I k` contributes `M(t,k)`; a field of type
`J (I k)` needs membership of that whole field type. The generic inverse
remains available for a later use. Keep its own antecedent atomic.

Carry an active-family check and a size budget through payload translation,
nested guards and any generated side axioms. Even a proof-only constructor
`roll : (exists _ : I, True) → I` re-enters the guard for `I` by translating
the existential. The current carrier reachability check misses that path.
An acyclic chain of records with two fields of the preceding type can also
double the output at each layer. The WHNF budget limits reduction during
matching and cannot bound the size of a formula.

Choose the fallback before emitting declaration axioms, constructor terms or
match equations for the selected problem. For a tagged family, including a
cyclic `CEnum`, keep the constructor tags. At re-entry or budget exhaustion
use the existing atomic membership of the field's full type. Constructor
typing must produce that atom and the shared guarded inverse must consume
it. In the `roll` example its existential payload then refers back to the
same membership atom. Incomplete constructor information permits ordinary
membership but cannot justify an exhaustive inverse.

For a subset candidate, check before erasing its constructor that the required
carrier guard and payloads can be emitted coherently within the expansion
bounds, including paths through proof quantifiers and nested types. If that
check fails or is inconclusive, use ordinary constructors and membership
consistently throughout the selected problem for that affected family.
Use that decision for constructor applications (including partial ones),
typing, matches and structural axioms. After choosing carrier erasure, a
per-occurrence budget cutoff must never switch a value back to a boxed
representation. Optional specialization can always be declined independently.

### 9.3 Placement in the emitted problem

For regular `Set`/`Type` families, start with §5(d) once per selected problem
and an atomic guard at each occurrence. Preserve the separate representation
rules for existing enums and subsets that pass the pre-emission check (§9.2). Collect candidate
specializations across the selected problem before emitting extra formulas.

| Candidate after index matching | Emission |
|---|---|
| Generic shape, many viable branches, or little simplification | Use the generic inverse and atomic guards. |
| Asserted local inhabitant yielding a small consequence | Keep its typing and attach the consequence once. A bounded local constructor case is also a candidate when a small surviving case has a visible field use in the goal, as described below. |
| Several occurrences benefit from the same reduced index pattern | Emit at most one guarded rule for the pattern. Each occurrence keeps its membership atom. |
| Every constructor provably clashes | The specialized consequence is false under the relevant membership and outer typing premises. |

For the local witness optimization, require **both** a small surviving case
under the §9.4 cost estimate and a goal term that visibly reads fields of
this inhabitant. Source projections on `h` and a match on `h` that uses a
data field are examples. A mention of the same record type, or projections
of a different value, does not qualify. In `R(left(h),right(h))`, first
try to state the constructor payload using those existing projections. Check
that each projection computes to the corresponding field on every viable
branch, preserving all field dependencies and branch premises. If that form
is unavailable and both admission conditions hold, expose the correlated
tuple once. Uses visible only through an unapplied lemma rely on shared
inversion. The visibility check concerns local witness expansion; a cheap
witness-free index consequence has its own admission path.

For example, if only one constructor can produce `I (S k)`, the shared
specialization can be

    ∀ k w. Nat(k) ∧ M(w,S(k)) → E_succ(w,k).

Here `E_succ` stands for the actual surviving branch printed on the
right-hand side. Neither it nor `M` asks for a new symbol. Two inhabitants
at `S k`, or inhabitants at `S k₁` and `S k₂`, can use this one rule.
Match again with symbolic `k` to justify the whole pattern. A branch
eliminated only at `S 0` could survive at `S k`.

Deduplicate rules within the selected problem, up to renaming of bound
variables. Sharing requires agreement on the family, retained parameter and
index patterns, erasure/arity, and all outer guards and residual constraints.
Close every free variable with its necessary premises. A fact depending on a
particular local hypothesis stays in that scope. If generalization cannot be
justified, use the generic inverse. Once a shared specialization covers the
uses, omit its per-inhabitant copies. Memoizing an OCaml syntax tree alone
would still print and clausify each copy. Keep the number and aggregate size
of extra rules bounded per problem. When many distinct index terms give
little reduction, fall back to the single generic axiom. If several local
typings justify the identical closed consequence `P(i)`, emit it once and
retain a sufficient source justification for reconstruction (§10.2).

### 9.4 ATP cost and polarity

For a closed, asserted inhabitant, existential fields at the outer level can
Skolemize to constants. The same fields under the generic inverse can become
Skolem functions of universally bound arguments. A small local case can thus
pay for itself. A function result under `∀u` can still require witnesses
depending on `u`, and a quantified proof payload can introduce functions of
its own. A disjunction leaves alternatives for the solver to resolve.

For a negative guard in a lemma, `∀w. (∃x. w=c(x) ∧ P(x)) → Q(w)` can
clausify as a rule about `Q(c(x))` without introducing a witness. A
conjecture is negated before refutation, which reverses its outer polarity.
Keep membership usable in both roles. An implication `M ⇒ C` licenses a
consequence for a known member. Replacing a guard throughout a problem
requires equivalence under its typing premises.

In a controlled Vampire clausification probe with eight constructors and
sixteen asserted inhabitants, shared inversion produced **40 clauses and
eight Skolem symbols**. Per-occurrence inversion produced **384 clauses and
128 Skolem symbols**, even with the generic rule omitted from that variant.
On a real two-field record, exposing a single small correlated pair let CVC4
prove a goal where shared inversion alone exhausted its run. These observations
motivate measuring both placements. E and Vampire work with the resulting
clauses and equalities. SMT backends receive quantified uninterpreted functions
and predicates, with no built-in dependent datatype semantics. An existing
family membership atom can provide a focused instantiation pattern. Price a
candidate by surviving branches, binder dependencies, estimated literals and
repeated uses. Also charge for the generic rule whenever other guards still
need it. [Probe formulas and solver results](reviews/spec-extraction-adversarial-review.md)

A finite rule can still generate an unbounded sequence of matching terms in
a solver. For example, inversion on a list value produces a membership for
a fresh tail, which may trigger inversion again. For the first evaluation,
admit an **extra shared recursive rule** only when each recursive membership
it can produce visibly decreases on an index. Use a fixed index position
along the recursive path and require a proper syntactic subterm after
checked substitution and bounded reduction, as in `M(t,k)` from
`M(w,S(k))`. For mutually recursive families this requires a consistent
decreasing measure across the cycle. If an emitted recursive membership is
unindexed, opaque or otherwise lacks that check, use generic inversion.
A terminal specialization with no recursive membership cannot retrigger
itself through a tail. This is an admission heuristic for extra rules; the
generic inverse and other quantified axioms can still generate terms.

Compare the generic-only and specialized runs on the same recursive problems,
including an unindexed family and vectors with ground and symbolic lengths.
Record timeout changes and, where each backend exposes them, generated term
depth and quantifier instantiations or saturation inferences. Keep input
budget and search cost as separate measurements.

### 9.5 Index unification at occurrences

Two rules currently read a constructor's result-index patterns `t̄ᶜ` against an
occurrence's actual indices `ū`:

  * **fording** (`ford_indices`, `coq_erasure.ml:239`) solves a field only when
    `t_rᶜ` is *literally* that field;
  * **rigid-clash pruning** (`rigid_clash`, `coq_transl.ml:927`) drops a case
    branch when `u_r` and `t_rᶜ` have distinct constructor heads somewhere
    along a spine of equal heads.

Use a one-sided matcher. Its unknowns are fresh constructor fields, and the
occurrence indices are rigid terms in the caller's context. Return either
`Clash` or a pair `(σ, residual equations)`. One constructor can solve
`n := k` from `S n = S k` and still require `f(k) = j` at a later index.

* Delete a syntactic identity. Solve a bare unknown by substitution throughout
  the telescope, payloads, constructor spine and all equations, including
  earlier residuals. Retain the instantiated field guard unless it follows
  from available premises.
* Decompose equal, saturated translated constructor heads at their injective
  payload positions. Retained parameters must coincide after substitution and
  bounded reduction, or be equal by explicit FOL equalities available in this
  scope. For example, injectivity of `d` gives `x=y` from
  `d(A,x)=d(B,y)`. With an independent premise `A=B`, congruence gives
  the reverse direction, so the matcher can keep `x=y` in place of the
  constructor equality. Record which equalities justified that step. An
  asserted hypothesis can justify a local consequence; an equation in one
  constructor disjunct is available only in that disjunct and must survive
  as a conjunct unless independently discharged. A shared rule using `A=B`
  must carry it as a premise or establish it from the rule's own premises.
  Exclude the equation being removed from the justification. If parameter
  agreement remains unresolved, retain the original equation under the
  substitution found so far.
* Drop a branch only for a certified clash of disjoint translated constructors.
  Proof terms and collapsed constructors cannot serve as rigid heads. Use
  budgeted head normalization on both sides. Preserve stuck equations for the
  ATP when the head, erasure or telescope is uncertain.

Apply matching at the level where the result will be shared. Formal indices
can already eliminate `∃n. i=n ∧ …` once in the declaration inverse for
`packet`. At the symbolic pattern `S k`, matching can remove a zero branch
and solve a predecessor once for every covered occurrence. Ground instances such as
`Fin.t 0` justify further pruning at their own scope. An empty set of viable
branches is useful information even when it leaves no index equations.

Initially cache only declaration analysis whose validity is independent of the
actual indices and local equality hypotheses. Retain the existing classifier's
parameter and typing-context distinctions. Give its templates fresh binders
when instantiating them. For each occurrence run the matcher on its actual
indices and its available equalities. Do not cache substitutions, clashes or
residuals in the classifier: `I 0` and `I (S k)` can have the same classifier
key and different viable branches. §9.3 deduplicates fully derived rules only
after all equality premises and local dependencies are known. Profile
repeated matching separately before considering a match-result cache.

The case path and the guard path should share telescope and substitution
machinery. Case-side pruning decides whether to emit a particular match
equation. Rewriting a guard used in both polarities must preserve its meaning.
Keep those proof obligations explicit at the call sites. The declaration mask
also needs the compatibility check in §10.3.

### 9.6 Rejected alternatives

The policy in §§9.1–9.4 uses the membership representation and constructor
symbols already emitted by the plugin. The following alternatives would add
structure to the ATP problem.

  * **An additional inhabitation predicate per family.** Sharing requires
    only the current membership in the antecedent of the inverse. Another
    predicate equivalent to it would add a bridge and another instantiation.

  * **Accessor symbols for forced fields** (Brady-style forcing with
    `n := pred(ī)`). This adds new symbols with defining equations the prover
    must rewrite with. §9.5 recovers the
    constructor-headed case with no new symbols. When the index is a variable,
    the field simply stays existential.
  * **Uniform constructor arity with `$Proof` placeholders**, to make
    informativeness masks independent of parameter instantiation. This
    contradicts the shallow translation's proof-erasure requirement (S4) and the pruning golden test
    (`check-extraction-transl.sh:132`). The mask disagreement it would address
    is §10.3, which requires a representation-compatibility check.
  * **Type-level functions as predicate definitions** (`T_F(c(…), x) ↔
    G(x, branch type)`). This makes each type-level function an inhabitation
    predicate with unfolding axioms.
    Type-level computation stays with translation-time head normalization
    under `opt_whnf_budget`.

## 10. Obligations and open items

### 10.1 Positive-position domain closure

The implication from membership to the complete constructor disjunction is
relative to the parameter and index guards of §5(d). A global `∀w. E(w,i)`
would impose domain closure on unrelated junk. Each specialized rule must
retain the premises needed to derive it. A ground fact may use the typing of
its actual local inhabitant. A filtered constructor list cannot justify
exhaustiveness. Keep the constructor typing and structural axioms that serve
atomic guards, recursive cutoffs and ordinary constructor equalities.
In particular, witnesses for the fields of each inhabitant do not establish
injectivity between two constructor terms.

### 10.2 Reconstruction

Associate each emitted axiom name with its source justification in the
selected problem. A local consequence records the originating inhabitant,
any local equality hypotheses used by matching, and the family whose
constructors justify the result. For a deduplicated closed fact, retain one
complete in-scope justification. A shared universally quantified rule
records its source family and premises; the concrete inhabitant for an
application comes from the membership evidence actually used in the proof.

After parsing the ATP core, recover these owners before hypothesis clearing.
A used `$_typeof_h` counts as use of the local `h`, including on the
generic-only path. Seed the existing local dependency closure with the
recovered inhabitants and equalities as well as the dependencies already
reported by the ATP. Supply the source family as an inversion hint when
recovering a constructor consequence. Carry this information with the
problem and its proof-core mapping, including evaluation replay, without
adding predicates or terms to the FOL.

Require the `packet` goal to reconstruct with the default
`Set Hammer ClearUnused` from both the baseline core and the local core
containing only `$_typeof_h` and the conjecture. The review reproduced
failure with clearing and success when `h` was retained. Also replay a
deduplicated fact with two possible owners and a specialization requiring a
local equality. Check that one sufficient justification survives clearing
and unrelated locals can still be cleared. [Reconstruction probe](reviews/spec-extraction-adversarial-review.md)

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

For a parameter-dependent index type, using the same function on the two
inputs can legitimately give different answers. In the review's
`indexed (A : Set) : A → Set` probe, the declaration used `mk(A,x)`, the
data occurrence used `mk(nat,0)`, and the proof occurrence used `mk(True)`.
A specialized rule must match the representation at every occurrence it
covers. Exercise mixed instantiations in the same dump and keep rules with
different erased spines separate. Include a matcher test with the same index terms in
two scopes, only one of which supplies the parameter equality. Check that
the unconditional output retains the residual equation and that every
generalized rewrite carries its justification.

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

1. **Shared inversion and matching.** Use the existing §5(d) as baseline.
   Screen fording in the shared inverse separately from occurrence-specific
   matching. Check solved-plus-stuck results, dependent field guards, mixed
   proof/data arities and incomplete telescopes. Bound re-entry before
   expanding any new family. Test the inhabited cyclic enum at different OCaml
   stack limits and require bounded output with the same shape. Test an unsafe
   subset candidate in one problem containing construction, a partial
   application and a match. All three must agree on its ordinary constructor.
2. **Small local consequences.** Compare shared inversion, local index
   facts and small field-dependent cases on the `packet` and two-projection
   examples. For local witness expansion require visible field use on the
   same inhabitant (§9.3). Include controls where the goal uses no fields
   or reads from a different inhabitant. Retain the source evidence needed
   for reconstruction.
3. **Shared index specializations.** Collect repeated reduced patterns within
   one problem and emit at most one guarded consequence per admissible pattern
   (§9.3). Compare this with the generic rule alone. Admit a specialization
   only when the simplification warrants the extra quantified formula. Use
   atomic tails and the decreasing-index condition of §9.4 for extra shared
   recursive rules.

Add translation-shape assertions to `check-extraction-transl.sh` for a regular
family with two distinct inhabitants of one fiber, then sixteen inhabitants of
a wide family. As inhabitants are added, count one generic inverse and their
membership facts. For a repeated profitable `S k` pattern, count one
specialized rule and zero copies of its branch body in the individual typing
axioms. Verify that two distinct inhabitants may carry different fields and
that a single inhabitant's two projections satisfy the constructor's joint
payload. Require the default-clearing core replays of §10.2. Include an
opaque membership consumer, an impossible fiber and a junk-model consistency
canary with an unrelated inhabitant.

Defer the four-prover evaluation until the upstream E status-filter fix is
available in the Hammer revision under test. E 3.5.11 prints
`% SZS status Theorem`; the affected filter accepts `# SZS` and drops that
success before reconstruction. After taking the fix, confirm a known theorem
through Hammer with only E enabled and the initial tactic shortcut disabled.
Require the E success to be recognized and the proof to reconstruct before
starting the four-prover comparison on the uniform setup.
[CoqHammer issue #238](https://github.com/lukaszcz/coqhammer/issues/238)

Screen each placement separately via `eval/rebuild-config.sh` on identical
premises, budgets and prover versions. Record translation time, FOF size, clausified literals
and clauses, fresh symbols and arities, prover-specific gains and losses, and
common goals reconstructed by any prover. Use the repeated-occurrence fixtures
to distinguish fixed rule cost from growth per inhabitant.

## 12. Verification status

The initial source reading covered the paths identified in §§1–7. The earlier
`Hammer_transl` check of `tagged`, `vec` and a two-field record used the
installed `6029473` plugin. The review at `27b80e8` checked the current
`tagged` behavior, dumped the regular `packet` and two-field record examples,
and measured hand-specialized copies of the same problems. The 40/384 clause
comparison in §9.4 is a synthetic clausification measurement. It does not
estimate corpus-wide success. Shared rules specialized at repeated index
patterns and the chosen admission conditions still need implementation and
evaluation. Numerical size thresholds and end-to-end impact remain open in §11. [Methods, raw formula shapes and results](reviews/spec-extraction-adversarial-review.md)
