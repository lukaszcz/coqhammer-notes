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
Updated 2026-11-20 against the Rocq 9.2 worktree at `27b80e8`, and revised
the same day after the second adversarial review. Revised 2026-11-22 after
the review of the implementation plan: rules are justified from the
declaration and not from the premises of one problem (§10.1), constructor
result indices are read by one reader (§§9.7, 10.4), first-order constructor
typing is a default (§9.1), local facts do not depend on premise selection
(§9.3), and every bound is local (§9.5). §§8–11 specify what to add
to the emitted ATP problem and to reconstruction. §12 gives the scope of the
measurements.*
[First review](reviews/spec-extraction-adversarial-review.md) ·
[Second review, with the prover tables](reviews/spec-extraction-adversarial-review-2.md)

## TL;DR

1. A regular family already gets a membership atom at each guard and one
   inversion axiom per declaration. That shape stays. Everything below is an
   addition to it (§8).
2. Fix reconstruction first; it needs no change to the translation. Keep the
   hypothesis whose typing axiom the ATP proof used, run the `dep: on`
   tactics second when the proof inverts an indexed data family, and accept
   `ContradictoryAxioms` as a found proof (§§10.2–10.3).
3. Drop from every elimination rule the parameter and index guards that its
   membership or predicate atom covers. Those guards are the measured
   bottleneck. This is a heuristic with one known inconsistency. State each
   data constructor's typing in direct first-order form as well; that is
   sound and discharges the guards that remain (§9.1).
4. For each family, indexed predicates included, emit rules specialized to
   the index patterns of its own constructors. They are a function of the
   declaration alone, and they introduce no new predicate or selector (§9.2).
5. For each goal hypothesis in a reduced fiber, also state its constructor
   form as a ground fact, iterated along a constructor-headed index. Emit it
   next to the pattern rules, not instead of them, and whether or not premise
   selection picked the family (§9.3).
6. A rule preserves the constructor's erased representation. One reader
   exposes the constructor heads of a result index and keeps every stuck
   term over the function the declaration names. Bound expansion through
   proof payloads as well as data fields, with bounds local to a declaration
   or a hypothesis (§§9.4–9.5, 9.7, 10.4).
7. A rule is emitted because it translates a fact provable from the
   declaration, not because the premises of one problem derive it (§10.1).
8. Compare each addition against the guard-free generic inverse with
   constructor typing, not against today's output. Measure problem size, ATP
   success and reconstruction (§§11–12).

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

**(a) Constructor typing** applies `G` to `c`'s own type. For a regular data
family, with parameters assumed well typed, its content is

    ∀ p̄ inf₀(c).  ⋀ⱼ G(aⱼ, Aⱼ)                   [informative fields]
                →  ⋀ⱼ ⟨Aⱼ⟩                       [propositional fields]
                →  $HasType( c(p̄, inf₀(c)), I(p̄, ⟦t̄ᶜ⟧) )

The **introduction** direction: to build a value you must discharge the
specification.

That schema is not what is printed. Under `opt_type_lifting` a constructor
with a product type gets a lifted membership atom, and the schema follows
only through the axioms that unfold it. For `S` the dump has

    $_typeof_S     $_arrow$t(nat, nat, S)
    $_arrow_N      ∀A B F. $_arrow$t(A,B,F) → ∀x. $HasType(x,A) → $HasType(F·x, B)
    $adef_S        ∀x. S·x = S$a1(x)
    $tdef_nat      ∀y. nat$t(y) ↔ $HasType(y, nat)

so `Nat(S n)` follows from `Nat(n)` in five inferences, through an arrow
axiom that unifies with every arrow-typed constant. A dependent constructor
such as `vcons` gets a lifted type symbol of its own, `$_type_N$t(vcons)`,
with its own unfolding axiom. One 1024-premise dump had 94 `$_arrow_*`
axioms and 515 `$adef_*` axioms. §9.1 is about this cost.

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

A `Prop`-sorted indexed predicate gets the same axiom without a subject
(`mk_prop_inversion`, `:787`, under `opt_prop_inversion_axioms`, default on):

    ∀ p̄ ī.  D(p̄,ī) ∧ I(p̄,ī)  →
        ⋁_c  ∃ inf₀(c).  ⋀ { G(aⱼ, Aⱼ) } ∧ ⋀ { ⟨Aⱼ⟩ } ∧ ⋀ { i_r = ⟦t_rᶜ⟧ }

For `ev 0`, `ev n → ev (S (S n))` the dump has
`∀i. Nat(i) → ev(i) → i = O ∨ ∃n. Nat(n) ∧ ev(n) ∧ i = S(S(n))`. There is no
constructor equation, because there is no proof object. A hypothesis
`h : ev t` is an axiom named `h`, with no typing axiom.

The patterns `⟦t_rᶜ⟧` are not always the source terms. A transparent
recursive function in a pattern is emitted over a fresh symbol (§10.4).

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
involved in expanding a guard (§9.5).

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

## 8. The baseline, and what this note adds

For a regular family `I`, write `M(h,i)` for the existing membership atom
and `E(h,i)` for the disjunction in §5(d), specialized at `i`. Both are
notation in this note. For example, with one constructor and a proof payload
depending on both fields, its case might be

    E(h,i) ≡ ∃ x y. G(x,A) ∧ G(y,B(x)) ∧ i=f(x,y) ∧ h=c(x,y) ∧ P(x,y).

Write `D` for the index guard and suppress the family parameters. At
`27b80e8` two hypotheses in one fiber already translate to three ground
facts and one quantified axiom.

    D(i)
    M(h₁,i)
    M(h₂,i)
    ∀ j w. D(j) ∧ M(w,j) → E(w,j).

`guard_leaf` returns the membership atom for a regular family (§6), and
`add_def_axioms` emits the last formula once per declaration (§5(d)). The
ATP can instantiate it at either inhabitant. Each instantiation has its own
witnesses, and all occurrences of `x,y` *within* a constructor case refer to
the same pair. Sharing witnesses across distinct inhabitants would
incorrectly identify their fields.

Keep this shape. The alternative writes `E(h₁,i)` and `E(h₂,i)` at the two
guards, copying the telescope, constructor equality and payload once per
*occurrence*. An occurrence is a request to generate a type guard, for
example the typing of a local hypothesis or the domain of a quantified
lemma. In a Vampire clausification probe with eight constructors and sixteen
asserted inhabitants, the shared form gave **40 clauses and eight Skolem
symbols**, and per-occurrence inversion gave **384 clauses and 128 Skolem
symbols**. That comparison is the reason not to regress. It prices an
expansion the current code does not perform for regular families, so it
measures nothing that this note adds.

**What the baseline costs.** The second review measured fourteen synthetic
goals that need inversion (§12 gives the limits of that evidence).

* *Provers.* On six `vec`/`fin` goals with 1024 premises and a 10 s limit,
  1 of 24 prover runs succeeds. On three `ev` goals, 0 of 12 do. The cause
  is the antecedent `D`: discharging `Nat(S n)` goes through the lifted
  typing of `S` (§5(a)).
* *Reconstruction.* On some slice, usually the 64-premise one, the ATPs
  prove all eleven data-family goals. Eight of them reconstruct. Three lose
  the inverted hypothesis to `ClearUnused`, and six succeed only through the
  `dep: on` tactics in the eighth tactic batch.

**What this note adds.** Each row is a change against `27b80e8`. A "cell"
is one prover on one goal at 1024 premises; the data-family suite has 24
cells and the `ev` suite 12. Rows are separate variants of the baseline
unless they say otherwise.

| § | Addition | Measured effect |
|---|---|---|
| 10.2 | Keep the hypothesis whose typing axiom the proof used; run `dep: on` second for indexed data families | The three clearing failures close with `hauto inv:` once the hypothesis is kept. Checked by direct tactic calls, not yet through `hammer`. |
| 10.3 | Accept `ContradictoryAxioms` | Once a specialized rule is present, Vampire reports it on both impossible-fiber goals in most runs. Those runs count as failures today. |
| 9.1 | Elimination rules without covered guards | Generic inverse alone: 1 → 10 of 24 and 0 → 5 of 12. |
| 9.1 | First-order typing of each data constructor | With it, guarded pattern rules reach the counts of the guard-free ones: 17 of 24 and 11 of 12. |
| 9.2 | Rules for the index patterns of the family's own constructors, predicates included | Guard-free: 17 of 24 and 11 of 12. Guarded: 15 and 8, with nothing proved at index depth 2. |
| 9.3 | Constructor form of a goal hypothesis as a ground fact | 17 of 24 alone, 20 together with pattern rules. At depth 2, one layer proves nothing and three layers serve all four provers. |
| 9.7, 10.4 | Index terms read by one reader: heads exposed, stuck terms as written | Probe over `fam (g x y)`: 0 of 4 as emitted, Vampire and CVC4 once the equation names `g`. A prototype of the reader names the source function in twelve fixtures and changes no existing test output. |
| 9.5 | Bounds on expansion | None. They protect output size and termination. |

§11 orders the work. The first two rows need no change to the translation.

## 9. Elimination rules

### 9.1 Covered guards are dropped

From here on the family is written inside the atom: `M(w, I p̄ ī)` stands for
`$HasType(w, I(p̄,ī))`.

Every elimination rule has a *family atom* in its antecedent: the membership
`M(w, I p̄ ī)` of a data family, or the atom `I(p̄,ī)` of a predicate. In the
intended model of `notes/type_guards.md` §3.1 that atom is false whenever a
parameter or index is not of the type its position forces. The same holds
hereditarily for the variables of a constructor-headed index pattern:
`M(w, vec A (S k))` forces `S k : nat`, which forces `k : nat`. The antecedent
guards on those variables are therefore *covered* in the sense of Tier A
(§3.3 there, whose worked example is the inversion of `le`). Drop them.

    ∀ p̄ ī w.  M(w, I(p̄,ī))  →  ⋁_c ∃ inf₀(c). …        [data family]
    ∀ p̄ ī.    I(p̄,ī)        →  ⋁_c ∃ inf₀(c). …        [predicate]

The rule applies to the generic inverse of §5(d) and to every pattern rule
of §9.2. A local fact (§9.3) has no antecedent.

* **What may be dropped.** An antecedent guard on a variable that occurs in
  the family atom, at a position reached through inductive type formers and
  constructors only, and whose forced type is a sort, a variable or a rigid
  application (the v1 restriction of `type_guards.md` §5.2). A guard that
  this test does not certify stays. Examples that stay: a variable occurring
  only under a defined function that may reduce, and an index whose formal
  type is a product.
* **What is kept.** Every guard in the consequent: the field guards under
  the existentials, and the guard of a solved field at its solution (§9.4).
  They are facts, and the prover uses them to discharge the guards of other
  premises. Dropping a guard conjunct under `∃` needs the stronger
  junk-falsity condition of `type_guards.md` §3.3, which this note does not
  use.
* **Where a guard stays, it is on a variable.** A pattern rule quantifies
  over the variables of its pattern, and a retained guard is the guard of
  one of them at its own type: `Nat(k)`, never `Nat(S (S k))`. The compound
  guard follows from it by constructor typing, and it is the compound form
  that the table below shows proving nothing at depth 2.

**Why.** Under `opt_type_lifting` the fact `Nat(S n)` takes five inferences
from `Nat(n)` (§5(a)). The generic inverse applied to `v : vec A (S n)`
needs it before it yields anything, and a guarded pattern rule applied at
`vec A 2` needs `Nat(S O)` again. Measured at 1024 premises:

| Variant | Data families (24) | `ev` (12) |
|---|---|---|
| Baseline | 1 | 0 |
| Generic inverse without parameter and index guards | 10 | 5 |
| Guarded pattern rules added | 15 | 8 |
| Guard-free pattern rules added | 17 | 11 |
| Guarded pattern rules and `∀x. Nat(x) → Nat(S x)` added | 17 | 11 |

In the last three rows the generic inverse keeps its guards. On the depth-2
goals the guarded rule gets 0 of 4 cells (`vec A 2`) and 1 of 4
(`ev (S⁴ n)`). The guard-free rule gets 2 and 4.

**Status of the argument.** The guarded rule is what §5(d) emits today, and
a guarded pattern rule is a consequence of it. The guard-free rule is not
derivable from the guarded one in FOL. The claim that it has the same truth
value in the intended model (`type_guards.md` §3.3, safety proposition) does
not hold in general. A selected equality between functions, proved by
functional and propositional extensionality, together with ordinary
unguarded lambda lifting makes a predicate true of every FOL value. The
guard-free inverse then collapses the domain, and a problem that had a
two-element countermodel is refuted (`evidence/semantics` of the
implementation plan). Guard dropping is therefore a deliberate heuristic.
It is on by default behind a switch, the limitation is documented, and the
switch is the opt-out for a user who meets ATP successes that do not
reconstruct. Write it into `add_inversion_axioms`, replacing the guarded
inverse in place: an appended guard-free copy doubles the non-Horn clauses
and the Skolem witnesses (`evidence/clauses`).

**First-order constructor typing.** The applied form of a constructor's
type,

    ∀ p̄ inf₀(c).  ⋀ⱼ G(aⱼ,Aⱼ) → ⋀ⱼ ⟨Aⱼ⟩ → M(c(p̄, inf₀(c)), I(p̄, ⟦t̄ᶜ⟧)),

is the constructor's type translated directly, so it needs no argument.
`add_typing_axiom` already emits this applied form for types with erasable
content (`coq_transl.ml:3077`). The last row of the table shows that with
it, guarded rules reach the counts of the guard-free ones on these probes.
Emit it by default for every data constructor, in the constructor's own
bundle and under its existing axiom name, next to the lifted membership.
It was first kept only as a control, for two reasons that do not hold up.
It covers constructor-headed index terms only: at `vec A (n + m)` the guard
`Nat(n + m)` still needs the lifted typing of `+`. That is why guard
dropping stays as well; it is no reason to leave the constructor-headed
case to a heuristic. And it adds one Horn clause per selected constructor.
That clause replaces a five-inference derivation for every guarded
premise, not only for inversions, and it gives a data family its
introduction rule in direct form. It has its own switch, and §11 measures
it on problems without indexed families too.

### 9.2 Pattern rules from the declaration's index cover

**Scope.** Every inductive with at least one informative index position
(§4) and an emitted inverse (§5(d)): regular data families, and `Prop`-sorted
indexed predicates under `opt_prop_inversion_axioms`. A predicate has the
same declaration-level inversion and the same index patterns as a data
family. It has no subject term, no constructor equation and no erased spine,
so it is the simpler case. Existing enums, subsets and empty types are out
of scope: their guards are already expanded (§6).

**The cover.** It is computed from the declaration alone. A *node* is a
tuple `π̄` of index patterns, one per informative index position, built from
constructors of the index types over distinct variables. The root is the
tuple of index formals `ī`. At a node, match each constructor's result
patterns against `π̄` with the matcher of §9.7, taking the constructor's
fields as unknowns and the node's variables as rigid. A constructor
*survives* at the node unless matching returns `Clash`. A survivor *demands
a split* of a node variable `k` when its residual equations contain
`k = d(…)` for a constructor `d` of `k`'s inductive type. Splitting `k`
replaces the node by one child per constructor `d′` of that type, with
`k := d′(fresh variables)`.

Build the tree breadth-first from the root, always splitting the leftmost
demanded variable. Stop at a node when no survivor demands a split, or when
a bound of §9.5 is reached. The order is fixed, so the result is a function
of the declaration.

**The rules.** The root's rule is the generic inverse. With the matcher
applied at the formals it solves a bare-variable pattern once, so `packet`
gets

    ∀ i h. M(h,i) → Nat(i) ∧ ∃ x y. Nat(x) ∧ Nat(y) ∧ P(i) ∧ h = pack(i,x,y).

For every other leaf `π̄` with variables `k̄`, emit

    ∀ p̄ k̄ w.  M(w, I(p̄,π̄))  →  ⋁_{c survives} ∃ inf(c). branch_c      [data family]
    ∀ p̄ k̄.    I(p̄,π̄)        →  ⋁_{c survives} ∃ inf(c). branch_c      [predicate]

where `inf(c)` are the fields that matching left unsolved and `branch_c` is
built as in §9.4. A leaf with no survivor gives the negated family atom,
`∀ p̄ k̄ w. ¬M(w, I(p̄,π̄))` or `∀ p̄ k̄. ¬I(p̄,π̄)`.

Omit a leaf's rule in four cases.

* It simplifies nothing: against the generic inverse at the same pattern,
  no constructor is eliminated and no field is solved.
* It says nothing: one survivor whose branch has no conjunct left. `ev(O)`
  is the example. A data family always keeps the constructor equation.
* It can retrigger itself: a survivor's branch contains a family atom of
  `I`, or of a family mutually recursive with it, whose index at the split
  position is not a proper subterm of the leaf's pattern (§9.6).
* It exceeds a size bound of §9.5.

Each rule is sound on its own, so omitting some leaves is safe.

**Examples.** The measured rules, written with the kept consequent guards.

    vec    ∀A w.   M(w, vec A O)      → w = vnil(A)
           ∀A k w. M(w, vec A (S k))  → Nat(k) ∧ ∃x u. G(x,A) ∧ M(u, vec A k) ∧ w = vcons(A,k,x,u)
    fin    ∀w.     ¬M(w, fin O)
           ∀k w.   M(w, fin (S k))    → Nat(k) ∧ (w = F1(k) ∨ ∃y. M(y, fin k) ∧ w = FS(k,y))
    ev     ¬ev(S O)
           ∀k.     ev(S (S k))        → Nat(k) ∧ ev(k)
    le     ∀n.     le(n, O)           → n = O
           ∀n k.   le(n, S k)         → n = S k ∨ (Nat(k) ∧ le(n,k))

`ev` needs depth 2: the first split gives `S k` with residual `k = S n`, and
the second gives `S O`, where `evSS` clashes, and `S (S k)`. With two index
positions the tree splits one position at a time. A typing judgment
`has_type Γ t T` splits on the term, and then on the type inside the leaves
where a constructor fixes it, which yields the usual inversion and
canonical-form lemmas.

**Why the declaration and not the occurrences.** The rules a family
contributes do not depend on which other premises were selected, or on how
often a pattern occurs. A clash or an injectivity step in the cover is
taken from the index type's declaration, which the translator always holds.
It does not wait for that type's discrimination and injectivity axioms to
be among the premises (§10.1).

* They are emitted where `$_inversion_I` is, under the same condition
  (every constructor telescope available, §5), and cached with the
  declaration's other axioms.
* One `hammer` call translates many problems. Each prover slice has its own
  state (`prepare_atp`, `provers.ml:457`), and `minimize` re-translates with
  the used dependencies only (`:492`). A rule admitted by counting
  occurrences across a problem can vanish from a smaller slice or from the
  minimized problem. A rule owned by the declaration is present whenever the
  generic inverse is.
* The cost does not justify counting. Clausified with E, the generic inverse
  of `vec` is 10 clauses, each with two positive literals. Its `S k` rule is
  3 Horn clauses (§9.6).

**The generic inverse stays.** It serves indices that are not
constructor-headed. The second review looked for a cost of keeping it next
to pattern rules it implies and found none: 15 cells with it and 15 without.

**Mixed representations.** Split only on index positions whose
informativeness does not depend on the parameters. For the rest the
declaration cannot fix one erased spine (§10.5), and the generic inverse is
all that is emitted. Split only on a variable whose type is a non-indexed
data inductive with every constructor available.

### 9.3 Local facts for goal hypotheses

**Admission.** Take each hypothesis `h` of the goal context whose type,
after bounded head reduction, is a saturated `I p̄ ū` for a regular data
family or an indexed predicate with every constructor telescope available.
Whether premise selection picked `I`'s declaration for this problem is not
consulted: the translator holds every accessible declaration, selected or
not. `h` is a data hypothesis with typing axiom `$_typeof_h`, or
a proof hypothesis of a predicate with axiom `h`. Match every constructor
against the actual indices `ū` (§9.7), with the asserted equalities of the
context available. Emit a local fact when

1. at most two constructors survive, and
2. the fiber is reduced: at least one constructor clashed, or `I` has a
   single constructor.

The shape of the goal is not consulted. Condition 2 excludes `n : nat` and
`l : list A`, where the fact would be a ground instance of the generic
inverse with nothing removed.

**The fact.** A separate axiom in `h`'s own bundle, closed and
unconditional under every guard policy, with `h` in place of the subject:

    ⋁_{c survives} ∃ inf(c). branch_c[w := h]

For a predicate hypothesis there is no subject and no constructor equation.
With no survivor the fact is `$false`. The existentials are outermost, so
the fields Skolemize to constants (§9.6).

Independently of conditions 1 and 2, a conjunct that mentions no unsolved
field and appears in every surviving branch may be asserted on its own. It
needs no witness, so a fiber with many survivors can still yield a fact.
With a single survivor the full fact already contains it, as it contains
`P(i)` for `packet`.

**Chains.** Suppose exactly one constructor survives and a field `u`,
informative or propositional, has type `I p̄ ū′` in the same family, where
each index in `ū′` is a subterm of the corresponding index in `ū` and at
least one is a proper subterm. Then expand `u` in place, under the same
existentials. Repeat while that holds, up to the layer bound of §9.5. A
layer with two survivors ends the chain as a disjunction whose fields are
not expanded. Every unexpanded field keeps its family atom. Each layer
consumes a constructor of an index term that is in the input, so the fact is
linear in that term. For `v : vec A 2`, leaving out the guards of the solved
fields:

    ∃x t. G(x,A) ∧ M(t, vec A 1) ∧ v = vcons(A,1,x,t)
      ∧ ∃y u. G(y,A) ∧ M(u, vec A 0) ∧ t = vcons(A,0,y,u) ∧ u = vnil(A)

For `h : ev (S⁴ n)` the chain is `ev(S (S n)) ∧ ev(n)`.

**Emit both.** A local fact is emitted whenever it is admitted, whether or
not a pattern rule covers the same fiber. The two placements serve different
provers. At 1024 premises the pattern rules alone solve 15 of 24 cells and
the one-layer facts alone 17. Together they solve 20. E proves four of the
goals with the rules and two with the facts. On the same four goals Z3 and
CVC4 take 8 of 8 cells with the facts and 4 of 8 with the rules. The cost of
a fact is three unit clauses (§9.6).

**Measured for the chain.** On the depth-2 goal `v : vec A 2 ⊢ ∃x y. v = …`
at 1024 premises, the one-layer fact solves 0 of 4 cells, alone, and 2 of 4
(Vampire, E) next to guard-free pattern rules. The three-layer fact above
solves 4 of 4 in both settings (Vampire 0.3 s, E 0.2 s, Z3 2.6 s, CVC4
1.3 s). On `ev (S⁴ n) ⊢ ev n` the one-layer fact `ev(S (S n))` alone solves
0 of 4. The two-layer chain was not run: it states the conjecture.

**Why it is safe.** A local fact states what inversion on `h` proves in the
goal context, where the actual indices are well typed. It is a closed
statement about constants of that context, as `$_typeof_h` is, so it needs
no antecedent guard. When the problem also contains the generic inverse,
the typing of the actual indices and the injectivity and discrimination of
the index constructors, the fact follows from them in FOL; emission does
not depend on that (§10.1).

**Ownership.** The fact is a function of the hypothesis, its type, the
local equalities matching used and the declarations. It is present in every
slice, and in the minimized problem whenever `h` is, also when the family's
own declaration is not among the premises. It is then the only place where
the specification of that hypothesis reaches the prover. A proof that uses
it uses `h` (§10.2).

**Not admitted.** A typing under quantifiers, such as a function result,
gets no local fact; the pattern rules serve it. A hypothesis of an enum,
subset or empty type needs none, because its typing axiom is already the
expansion (§6). Global constants of indexed type are left out of the first
version.

### 9.4 Building a branch

A rule or fact is built per surviving constructor `c` from the matcher's
result `(σ, residual equations)`. `σ` contains the solved fields and the
proof erasures. Bind the unsolved informative fields in telescope order. The
branch is the conjunction of

* the equality of the subject with the translated **full** constructor spine
  under `σ` (data families only),
* the guard of each informative field at its instantiated, possibly
  dependent type, including a solved field at its solution,
* each translated proof payload under the same substitution and binders, and
* the residual index equations.

Existentially close each branch and disjoin the branches.

Three points carry over from the first review. A solved field stays in its
slot of the constructor term: for `h : packet i` the term is `pack(i,x,y)`,
never a binary `pack(x,y)`. The guard of a solved field is retained, because
a bare FOL subterm carries no sort certificate; with the antecedent guards
gone (§9.1) it appears in the consequent, as `Nat(k)` does in the rules of
§9.2. And the witnesses are shared within a branch: in §8, the guard for `y`
depends on `x`, and the index, constructor and `P(x,y)` must all refer to
the same pair. Separate claims that some pair satisfies `P` and some pair
constructs `h` would lose the correlation needed to prove
`P(left(h),right(h))`.

A conjunct that mentions only indices and parameters needs no witness. With
a single surviving branch it clausifies to a clause of its own, as `P(i)`
does for `packet`.

### 9.5 Bounds

**Numeric bounds.** These are initial values. Each is an option, to be tuned
on the corpus (§11).

| Bound | Initial value | Why this value |
|---|---|---|
| Split depth along one index position | 2 constructor layers | The least depth that reaches `ev`'s pattern `S (S n)`. |
| Total size of a family's pattern rules | 4 × the size of its generic inverse | A leaf rule of `vec` is about a quarter of the inverse in literals (§9.6). |
| Estimated clauses of a family's pattern rules | 4 × the estimate for its generic inverse | Bounds the case where constructors survive in many leaves. |
| Work on one family's cover | 16,384 visited term nodes | Protects translation time. |
| Survivors in a local fact | 2 | Every measured fact had one or two branches. |
| Layers in a local chain | 8 | A layer adds three unit clauses. |
| Work and size of one local fact | 4,096 nodes each | A chain is linear in an index term of the input. |
| Exposure of one index pattern | 256 nodes | A closed `Nat.pow 2 9` index otherwise becomes a 512-successor numeral (§10.4). |
| Symbols in one expanded guard, nested payloads included | twice the largest expansion among the existing fixtures | Start from `tests/plugin/EXPECTED-extraction.md`. |

**Every bound is local** to a declaration, a hypothesis or a pattern. Total
output is then linear in the selected families and the hypotheses, and no
rule's presence depends on another declaration. An allowance shared across
one problem would make a family's rules depend on the other premises and
differ in the minimized problem (§9.8).

**No cap on the number of leaves.** Where an index separates the
constructors, each constructor survives in one leaf, so all leaf rules
together are about the size of the generic inverse, whatever their number.
A cap of twelve would stop the cover on exactly the wide typing and step
judgments whose generic inverse is the worst clause set. The size and
clause allowances bound the other case.

A split is atomic: it is admitted only if the rules of all its children fit
what remains of the family's allowances, and otherwise the node stays a
leaf. When a bound stops a chain, the tail keeps its membership atom.

**Atomic membership below one layer.** Use the atomic membership for regular
data fields at the next constructor layer. A recursive tail `t : I k`
contributes `M(t,k)`; a field of type `J (I k)` needs membership of that
whole field type. The chain of §9.3 is the one exception, and its length is
bounded by a term of the input. The generic inverse remains available for a
later use.

**Re-entry.** Carry an active-family check and the symbol budget through
payload translation, nested guards and any generated side axioms. Even a
proof-only constructor `roll : (exists _ : I, True) → I` re-enters the guard
for `I` by translating the existential. The current carrier reachability
check misses that path. An acyclic chain of records with two fields of the
preceding type can also double the output at each layer. The WHNF budget
limits reduction during matching and cannot bound the size of a formula.

Choose the fallback per declaration, before any of its declaration axioms,
constructor terms or match equations is emitted. For a tagged family,
including a cyclic `CEnum`, keep the constructor tags. At re-entry or budget
exhaustion use the existing atomic membership of the field's full type.
Constructor typing must produce that atom and the generic inverse must
consume it. In the `roll` example its existential payload then refers back
to the same membership atom. Incomplete constructor information permits
ordinary membership but cannot justify an exhaustive inverse.

For a subset candidate, check before erasing its constructor that the
required carrier guard and payloads can be emitted coherently within the
bounds, including paths through proof quantifiers and nested types. If that
check fails or is inconclusive, use ordinary constructors and membership for
that family: in constructor applications (including partial ones), typing,
matches and structural axioms. The decision is a function of the declaration
and the classifier's parameter class. It does not depend on which premises
are selected, so every slice and the minimized problem agree on it. After
choosing carrier erasure, a per-occurrence budget cutoff must never switch a
value back to a boxed representation. A pattern rule or a local fact can
always be declined independently.

### 9.6 ATP cost and polarity

**Measured sizes.** Clausified with E (`--cnf --no-preprocessing`) for
`vec`:

| Formula | Clauses | Literals | Skolem symbols | Shape |
|---|---|---|---|---|
| Generic inverse | 10 | 50 | 3, arity 3 | every clause has two positive literals |
| `S k` pattern rule | 3 | 12 | 2, arity 3 | Horn |
| Local fact for `v : vec A (S n)` | 3 | 3 | 2 constants | ground units |

The measured rule did not carry the kept guard `Nat(k)` of §9.4, which adds
one Horn clause.

**Skolemization.** For a closed, asserted inhabitant, existential fields at
the outer level Skolemize to constants. The same fields under a quantified
rule become Skolem functions of the universally bound arguments. That is why
a local fact can pay for itself next to a rule that implies it. A quantified
proof payload can still introduce functions of its own, and a disjunction
leaves alternatives for the solver to resolve.

**Polarity.** For a negative guard in a lemma,
`∀w. (∃x. w=c(x) ∧ P(x)) → Q(w)` can clausify as a rule about `Q(c(x))`
without introducing a witness. A conjecture is negated before refutation,
which reverses its outer polarity. Keep membership usable in both roles. An
implication `M ⇒ C` licenses a consequence for a known member. Replacing a
guard throughout a problem requires equivalence under its typing premises,
and nothing in §9 does that for a regular family.

**What the provers receive.** E and Vampire work with the resulting clauses
and equalities. SMT backends receive quantified uninterpreted functions and
predicates, with no built-in dependent datatype semantics. The family atom
in a rule's antecedent gives them a focused instantiation pattern, and the
ground fact needs no instantiation at all.

**Term generation.** A finite rule can still generate an unbounded sequence
of matching terms. Inversion on a list value produces a membership for a
fresh tail, which may trigger inversion again. The generic inverse of an
unindexed recursive family is already such a source, and it stays. A pattern
rule must not add another: it is emitted only when each recursive family
atom it can produce decreases on an index, as `M(u, vec A k)` from
`M(w, vec A (S k))` does (§9.2). Use a fixed index position along the
recursive path and require a proper syntactic subterm after checked
substitution and bounded reduction. For mutually recursive families this
requires a consistent decreasing measure across the cycle. A rule with no
recursive atom cannot retrigger itself.

Compare the runs with and without the new rules on the same recursive
problems: an unindexed family, vectors with ground and symbolic lengths, and
a problem in which a pattern rule is present and the generic inverse fires
anyway. Record timeout changes and, where each backend exposes them,
generated term depth and quantifier instantiations or saturation inferences.
Keep input size and search cost as separate measurements.

### 9.7 Index matching

Two rules currently read a constructor's result-index patterns `t̄ᶜ` against
actual indices `ū`:

  * **fording** (`ford_indices`, `coq_erasure.ml:239`) solves a field only
    when `t_rᶜ` is *literally* that field;
  * **rigid-clash pruning** (`rigid_clash`, `coq_transl.ml:927`) drops a case
    branch when `u_r` and `t_rᶜ` have distinct constructor heads somewhere
    along a spine of equal heads.

Use a one-sided matcher. Its unknowns are fresh constructor fields, and the
other side consists of rigid terms in the caller's context. Return either
`Clash` or a pair `(σ, residual equations)`. One constructor can solve
`n := k` from `S n = S k` and still require `f(k) = j` at a later index.

* Delete a syntactic identity. Solve a bare unknown by substitution
  throughout the telescope, payloads, constructor spine and all equations,
  including earlier residuals. Retain the instantiated field guard (§9.4).
* Decompose equal, saturated translated constructor heads at their injective
  payload positions. Retained parameters must coincide after substitution
  and bounded reduction, or be equal by explicit FOL equalities available in
  this scope. For example, injectivity of `d` gives `x=y` from
  `d(A,x)=d(B,y)`. With an independent premise `A=B`, congruence gives the
  reverse direction, so the matcher can keep `x=y` in place of the
  constructor equality. Record which equalities justified that step. An
  asserted hypothesis can justify a local fact; an equation in one
  constructor disjunct is available only in that disjunct and must survive
  as a conjunct unless independently discharged. Exclude the equation being
  removed from the justification. If parameter agreement remains unresolved,
  retain the original equation under the substitution found so far.
* Drop a branch only for a certified clash of disjoint translated
  constructors. Proof terms and collapsed constructors cannot serve as rigid
  heads. Use budgeted head normalization on both sides. Preserve stuck
  equations for the ATP when the head, erasure or telescope is uncertain.
  The certificate is read from the index type's declaration: constructors
  of one data inductive, saturated, not collapsed, with a determined proof
  mask. Whether that type's discrimination axiom is among the premises is
  not part of it (§10.1).
* Apply the viability test even when matching removes the last residual
  equation. An empty set of surviving branches is information: it is the
  negated-atom rule of §9.2 and the `$false` fact of §9.3.

**Heads are exposed, stuck terms are emitted as written.** A result index
is read by head reduction on a copy. A variable is kept; under a
constructor head the informative arguments are read the same way; any
other term goes into the equation as the declaration wrote it. So `g x y`
stuck gives `i = g(x,y)` over the named function, `S n + m` gives
`i = S(n + m)` with `+` still named, and `id n` gives the bare field `n`.
Today a transparent recursive function is emitted over a fresh symbol
instead (§10.4). A residual equation is only usable by the ATP if it
mentions the symbol that occurrences and lemmas mention. One reader does
this for every consumer of result indices: the inversions, the
classification and fording, the guard equations of enums and subsets, the
case path, and the constructor's own axiom. Occurrence indices elsewhere
stay as their source has them.

**Where it runs.**

* *At the declaration*, for the root and the nodes of the cover (§9.2). The
  rigid side is the node's patterns. No local equality is available, so a
  parameter disagreement leaves the original equation in the rule.
* *At a goal hypothesis*, for a local fact (§9.3). The rigid side is the
  actual indices, and the equalities asserted in the context may justify a
  step. Those equalities then belong to the fact's justification (§10.2).
* *On the case path*, as today, to decide whether to emit a match equation.

A guard of a regular family elsewhere, for example in the domain of a
quantified lemma, keeps its membership atom and is not matched. The ATP
applies the rules to it.

Cache declaration analysis, the cover included, with the declaration. Its
validity is independent of actual indices and local equalities. Retain the
existing classifier's parameter and typing-context distinctions, and give
its templates fresh binders when instantiating them. Do not cache a
hypothesis's substitutions, clashes or residuals in the classifier: `I 0`
and `I (S k)` can have the same classifier key and different survivors.

The case path and the rule path should share telescope and substitution
machinery. Case-side pruning decides whether to emit a particular match
equation. A rule or fact asserts an implication from the family atom and
must be justified as one. Keep those proof obligations explicit at the call
sites. The declaration mask also needs the compatibility check in §10.5.

### 9.8 Rejected alternatives

The policy in §§9.1–9.7 uses the membership representation and constructor
symbols already emitted by the plugin. The first four alternatives would add
structure to the ATP problem. The next four were in the previous revision of
this note and are withdrawn. The ninth was considered for the second
revision. The last four were considered in the review of the implementation
plan.

  * **An additional inhabitation predicate per family.** Sharing requires
    only the current membership in the antecedent of the inverse. Another
    predicate equivalent to it would add a bridge and another instantiation.
  * **Accessor symbols for forced fields** (Brady-style forcing with
    `n := pred(ī)`). This adds new symbols with defining equations the prover
    must rewrite with. §9.7 recovers the constructor-headed case with no new
    symbols. When the index is a variable, the field simply stays
    existential.
  * **Uniform constructor arity with `$Proof` placeholders**, to make
    informativeness masks independent of parameter instantiation. This
    contradicts the shallow translation's proof-erasure requirement and the
    pruning golden test (`check-extraction-transl.sh:132`). The mask
    disagreement it would address is §10.5, which requires a
    representation-compatibility check.
  * **Type-level functions as predicate definitions** (`T_F(c(…), x) ↔
    G(x, branch type)`). This makes each type-level function an inhabitation
    predicate with unfolding axioms. Type-level computation stays with
    translation-time head normalization under `opt_whnf_budget`.
  * **Collecting index patterns across the selected problem.** A rule
    admitted because several occurrences share a pattern makes one premise's
    output depend on the other premises, has no place in the per-declaration
    axiom cache, and can disappear under minimization. The declaration's
    cover (§9.2) needs none of that.
  * **One placement per fiber.** Withdrawing the local fact when a shared
    rule covers it loses the cells that only the fact solves (§9.3).
  * **Admitting a local fact only when the goal visibly reads the fields.**
    Read literally, that admits one of the four probe goals on which the fact
    helped. The others state a canonical form or read the fields in a
    hypothesis.
  * **Stating a payload through existing projections**, as in
    `R(left(h),right(h))`, to avoid witnesses. It needs a check that each
    projection computes to the right field on every surviving branch. The
    local fact gives the same correlation with Skolem constants. Reconsider
    only if those constants turn out to hurt.
  * **Dropping the generic inverse when the cover is complete.** No cost of
    keeping it was measured, and it serves indices that are not
    constructor-headed.
  * **Emitting a rule only when the premises of the same problem derive
    it.** A pattern rule of `ev` would then exist only in problems that also
    selected `nat`, and could vanish from the minimized problem. It needs an
    index of delivered formulas and a dependency map that replay cannot
    recover from axiom names. It buys no soundness: every axiom emitted
    today is justified from its declaration (§10.1).
  * **A work or size allowance shared across one problem.** It makes one
    family's rules depend on which other families were selected, and it
    needs a global pass over a translation organised by declaration. Local
    bounds already make the output linear (§9.5).
  * **Switching guard dropping off in a problem that contains an equation
    between functions.** It blocks the known inconsistency by its mechanism.
    It also makes an inverse depend on the other premises, and it is not
    known to be the only route to a predicate that holds of junk. The
    limitation is documented instead (§9.1).
  * **First-order constructor typing only as an evaluation control.** It is
    sound, costs one Horn clause per selected constructor and serves every
    guarded premise (§9.1).

## 10. Obligations and open items

### 10.1 Soundness and domain closure

The implication from a family atom to the constructor disjunction is all
that any rule here asserts. A global `∀w. E(w,i)` would impose domain
closure on unrelated junk. A filtered constructor list cannot justify
exhaustiveness. Keep the constructor typing and structural axioms that serve
atomic guards, recursive cutoffs and ordinary constructor equalities. In
particular, witnesses for the fields of each inhabitant do not establish
injectivity between two constructor terms.

**The basis of a rule.** A formula is emitted because it translates a
statement provable in Rocq from the inductive declaration, or for a local
fact from the goal context, at the erased representation the translator
uses. That is the basis of every axiom emitted today, the generic inverse
included: none of them is derived from the other formulas of the problem.
A new rule does not have to be either. Three things follow.

* A declaration's rules are a function of the declaration and the options.
  They are identical in every problem that contains the declaration, the
  minimized one included.
* Disjointness and injectivity of index constructors are used wherever the
  translator would state them for those constructors, whether or not the
  index type's own axioms were selected.
* No index of delivered formulas and no dependency map is needed. An
  axiom's owners are read from its name (§10.2).

What a rule must still satisfy is a **representation condition**: it is
stated on the spines, proof masks and constructor symbols the translator
emits for every value it covers (§§9.7, 10.5).

| Formula | Justification |
|---|---|
| Guarded generic inverse, first-order constructor typing | The declaration, translated. Emitted today, or the direct form of what is. |
| Guarded pattern rule | The declaration: inversion at the pattern, with disjointness and injectivity of the index constructors. |
| Local fact | The goal context: inversion on the hypothesis. A step justified by a local equality depends on that equality. |
| Guard-free generic inverse and pattern rule | A heuristic. Not derivable from the guarded form, and inconsistent with a selected extensional function equality (§9.1). |

Because rules other than the guard-free ones no longer need a derivation
from the problem, the consistency lists of §11 also run with guard dropping
off and every other rule on. A refutation there cannot be blamed on the
heuristic.

The negated-atom rule of an empty fiber is false of no inhabitant, because
the fiber has none. A problem containing both the rule and an inhabitant of
that fiber is inconsistent, as it should be. A satisfiable context must stay
satisfiable: pair every impossible-fiber fixture with a canary that holds an
unrelated inhabitant (§11).

### 10.2 Reconstruction

**Ownership by name.** The source of an emitted axiom must be recoverable
from its name alone, because evaluation replay sees only the names in a
prover's output.

| Axiom | Name | Recovered from the name |
|---|---|---|
| Generic inverse | `$_inversion_<ind>` | inversion hint `<ind>` |
| Pattern rule | `$_inversion_<ind>$<n>`, `n` the leaf's ordinal | inversion hint `<ind>` |
| Typing of a local `h` | `$_typeof_<h>` | owner `h` |
| Local fact | `$_hinv_<h>$<ind>`, then `$<e>` per local equality `e` that matching used | owners `h` and each `e`, inversion hint `<ind>` |

`Atp_names.get_inversions` returns the raw suffix today (`atp_names.ml:47`),
so it must strip from the first `$`, as `get_typings` does (`:41`). The
`$_hinv_` prefix needs its own reader, which splits the suffix at `$`.
Hypothesis and inductive names contain no `$`.

**Clearing.** After parsing the ATP core, recover the owners before
hypothesis clearing. A used `$_typeof_h` or `$_hinv_h$…` counts as use of
the local `h`, including on the generic-only path. `get_tac_args` builds
`used_ids` from `info.deps` only (`hammer_main.ml:404`); seed it with the
recovered owners. The existing closure over hypothesis dependencies then
applies. `get_atp_deps` already counts typings (`provers.ml:184`), so
minimization keeps the owner of a `$_typeof_` axiom. Add the family of a
used `$_inversion_` axiom there, which is missing today. Do not add a family
named only by a `$_hinv_` axiom: the fact travels with `h`, and its family
may not be among the premises. A shared rule has no owner of its own: the
inhabitant it was applied to comes from the membership evidence in the
core.

The second review found three goals of eleven that the ATPs prove and that
fail here: `packet n → P n`, `fin 0 → False` and `appf k → ∃n m. k = f n m`.
With the hypothesis kept, `hauto inv: packet`, `hauto inv: fin` and
`hauto inv: appf` close them with no axiom beyond the probes' own
parameters, the first in 0.01 s. After `clear h`, `hauto inv: packet`
fails.

**Routing.** Six further goals over `vec` and `fin` reconstruct only with
the `dep: on` tactics. Plain `hauto` with the inversion hint fails or
exceeds 20 s on four of them, and `hauto lq: on dep: on` closes each in
under 0.05 s. Those tactics form the eighth batch (`hammer_main.ml:732`).
One call ran the first seven batches to their limits and took 36.6 s.

When the inversion hints include an indexed data family, that is, an
inductive outside `Prop` with at least one index, run the `dep: on` batch
second. The first batch is unchanged. The delay before `dep: on` starts is
then at most one `ReconstrLimit` (5 s by default). A predicate needs no
routing: all three `ev` goals reconstruct with plain `hauto … inv: ev`. The
implementation plan evaluates the reordering as an experiment and adopts it
only if no stable axiom-free proof is traded for one that uses the axiom
below.

**Directed inversion.** A core that names `$_hinv_h$…`, or `$_typeof_h`
next to an inverse of `h`'s family, says which hypothesis the prover
inverted. The hint alone leaves the tactics to rediscover it. As an
experiment, run the first batch's tactics once more after `sinvert h`, or
`sdepinvert h` for an indexed data family, and compare closures, time and
assumptions. For an empty fiber the inversion alone closes the goal.

**Axiom.** The `dep: on` proofs depend on `Eqdep.Eq_rect_eq.eq_rect_eq`
(`Print Assumptions` on four of the reconstructed goals). This is already so
today, in the last batch. With the routing above, a proof uses the axiom
only when the axiom-free first batch has failed. Putting `dep: on` into the
first batch was rejected: a batch runs in parallel and its first finisher
wins, so `hammer` would return an axiom-dependent proof where an axiom-free
one exists. Axiom-free dependent inversion for index types with decidable
equality is tactic work in the `sauto` package and is outside this note.

**Replays.** A specialized core is smaller than a generic one: 5 axioms
against 12 on one probe, and it no longer mentions `O_S` or `neq_succ_0`.
Run every replay against cores produced with the new rules. Require:

* the `packet` goal with the default `Set Hammer ClearUnused`, from the
  baseline core and from the core containing only `$_typeof_h` and the
  conjecture;
* a core containing a pattern rule name, and one containing a `$_hinv_`
  name, each yielding the hint and the owner;
* a local fact that needed a local equality, with both owners surviving
  clearing and unrelated locals still cleared;
* a `vec` goal reconstructed in the second batch.

### 10.3 Prover status

A proof from an impossible fiber does not need the conjecture. Once
`¬M(w, fin O)` or a `$false` fact is in the problem, Vampire reports
`SZS status ContradictoryAxioms` for `x : fin 0 ⊢ False` and for
`ev 1 → False` in most runs; the status depends on which strategy finishes
first. E reports it for the `fin 0` goal on the 64-premise problem, already
on today's translation. Z3 and CVC4 report `Theorem`. `invoke_prover`
accepts only `SZS status Theorem` (`provers.ml:204`), so the two saturation
provers count as failures on exactly the goals this note makes easy.

Accept `ContradictoryAxioms` as a found proof and let reconstruction decide.
Both provers print the refutation with axiom names. On the `fin 0` probe
with a hand-written rule `$_inversion_Defs.fin$O`, Vampire's proof at 1024
premises and E's at 64 both list that rule and `$_typeof_x`, so the core is
recovered as usual. E's output filter must also pass its `% SZS` lines
(§11). E did not solve that goal at 1024 premises in any variant, which was
not investigated.

In evaluation, record the status. A `ContradictoryAxioms` core with no axiom
from the goal context means the selected premises are inconsistent on their
own. Count it as a consistency hit; the canaries already do
(`check-consistency.sh:286`). The consistency stage of the evaluation
rewrites the conjecture to `$false` and keeps the goal's hypotheses, so its
curated list must not contain a lemma with a hypothesis in an empty fiber.

### 10.4 Defect: function-valued index patterns over a fresh symbol

Independent of this proposal, and a precondition for §9.7. Constructor types
are read through `Coq_typing.destruct_type_app`, which evaluates the whole
type to normal form. A transparent recursive function in a result pattern is
unfolded to its `Fix`. When the fixpoint is stuck, the anonymous `Fix` is
reified and lifted again under a fresh name. For
`mkfam : ∀x y, fam (g x y)` the emitted inverse is

    ∀i w. T(i) → M(w, fam i) →
      ∃x y. T(x) ∧ T(y) ∧ i = $_fix_58(i, x, y) ∧ w = mkfam(x,y).

The fresh symbol has its own copy of `g`'s defining equations and takes the
index variable `i` as a spurious argument. Nothing but induction relates it
to `g(x,y)`, which is the term every occurrence and lemma uses.
`app2 : … → app2 (n + m)` gets `i = $_fix_688(i, n, m, n, m)` in the same
way. On a probe that needs the equation, no prover succeeds on the problem
as emitted. With `g(x,y)` substituted by hand in that one axiom, Vampire and
CVC4 prove it in 5.4 s each. A control over an opaque function takes them
6.0 s and 8.0 s.

The same holds for a predicate. For `st : stepv (n * m) (S n + m)` the
constructor's own axiom states `stepv(mul(n,m), add(S(n),m))`, and the
inverse states `i = $_fix_600(i,j,n,m)` and `j = S($_fix_516(i,j,n,m))`:
the introduction and the elimination of one predicate share no function
symbol. The evaluation is also unbounded. A closed index `Nat.pow 2 9`
becomes a 512-successor numeral, written twice into one 30 KB inverse.
Field types do not show the artifact: binder types are reified unevaluated,
and only the result application is evaluated.

**The fix is one reader** for the patterns, used in the three places that
read them: the two inversions (`coq_transl.ml:758`, `:793`) and
`constructor_index_data` (`coq_erasure.ml:155`), which serves fording,
classification and the case path. The constructor's own axiom is translated
from the same reading.

1. Refresh the binders of the declared type once and peel its product
   telescope without evaluating it.
2. Read each result index by head reduction on a copy (§9.7): keep a
   variable; under a constructor head read the informative, non-parameter
   arguments the same way; return anything else as written. This keeps what
   normalization was good for. `S n + m` still shows its `S`, and `id n` is
   still the bare field that fording solves.
3. Refold named fixpoints during head reduction. The head carries the
   folded term it came from, the unfolded constant applied to the arguments
   consumed since. A fixpoint unfolds with its own name bound to that term
   and not to the anonymous block. A stuck elimination is returned folded;
   a variable or constructor head is returned as it is.
4. Fall back to the written pattern when the reduction budget or a limit of
   256 exposed nodes runs out, and when the result would contain an
   anonymous fixpoint or match that the written pattern does not. Exposure
   then never introduces a lift the declaration did not have.

A prototype of these four steps was run on twelve fixtures
(`evidence/index-terms` of the implementation plan). Stuck and partially
reducing fixpoints keep their names, including a `fun A => fix …` function
refolded with its parameter. The other component of a mutual block, a
fixpoint hidden inside a definition and the exposure limit each fall back
to the written term. No anonymous lift remains, and the inverse and the
constructor axiom agree in every fixture. With the reader on, the existing
test suites pass and none of the 631 axiom lines of twelve existing
translation test files changes. The lifts that remain elsewhere take dead
context arguments (`$_fix_35(i, n, m)` never reads `i`); that is a separate
defect.

### 10.5 Defect: two implementations of "informative index position"

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
inputs can legitimately give different answers. In the first review's
`indexed (A : Set) : A → Set` probe, the declaration used `mk(A,x)`, the
data occurrence used `mk(nat,0)`, and the proof occurrence used `mk(True)`.
A rule must match the representation at every inhabitant it covers. The
cover therefore splits only on positions whose informativeness is fixed by
the declaration (§9.2), and a local fact uses the mask of its own
hypothesis. Exercise mixed instantiations in the same dump. Include a
matcher test with the same index terms in two scopes, only one of which
supplies the parameter equality. Check that the unconditional output retains
the residual equation and that every step justified by an equality records
it.

### 10.6 Defect: stale premise in `notes/gaps.md` §7

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

### 10.7 Defect: CVC4 time limit

`call_cvc4` passes `--tlimit <ATPLimit>` (`provers.ml:353`). CVC4 1.8 reads
that flag in milliseconds, and in practice does not enforce it: `cvc4
--tlimit 10` ran 41 s on one probe until an outer timeout killed it. CVC4's
budget is therefore whatever `htimeout` allows. Pass milliseconds, and until
then record in every evaluation that CVC4 runs to the outer limit.

### 10.8 Scope limit: indices that are types

`rigid_clash` fires on term constructors only. For a family indexed by a
type, such as `expr : Type → Type`, every branch survives with an equation
like `i = nat`, and nothing in the problem separates `nat` from `bool`. The
matcher of §9.7 inherits this: it drops a branch only for a certified clash
of disjoint translated constructors. The cover never splits on a
sort-typed index position. Such families get the generic inverse and no
more.

## 11. Staging

The order follows measured value per unit of work. Stages 0 and 1 leave the
translation unchanged.

0. **Reconstruction.** Owners by name, clearing, and `dep: on` in the second
   batch (§10.2). Expected from the direct tactic checks: the eleven
   data-family probes go from 8 to 11 reconstructed. Run them through
   `hammer` to confirm.
1. **Prover status.** Accept `ContradictoryAxioms` (§10.3). Assert it end to
   end on `x : fin 0 ⊢ False` with only Vampire enabled.
2. **Guards.** The guard-free generic inverse and first-order constructor
   typing, each behind its own switch and both on by default (§9.1).
   Evaluate each alone and both together on the corpus. Every later stage
   is compared against the two together, and reported against constructor
   typing alone, not against today's baseline.
3. **Index terms.** The reader of §10.4, behind its own switch and on by
   default, starting from the prototype. Fixtures: the twelve of the
   prototype, with an assertion on the symbol in each index equation. Then
   implement the matcher (§9.7) and screen it at the root: solved-plus-stuck
   results, dependent field guards, mixed proof/data arities and incomplete
   telescopes.
4. **Pattern rules for predicates** (§9.2). No subject, no spine, no mask
   question and no reconstruction cost.
5. **Pattern rules and local facts for data families** (§§9.2–9.3), emitted
   together.

Bound re-entry (§9.5) before any stage that expands a new family. Test the
inhabited cyclic enum at different OCaml stack limits and require bounded
output with the same shape. Test an unsafe subset candidate in one problem
containing construction, a partial application and a match. All three must
agree on its ordinary constructor.

**A census comes with stage 4.** The cover computation classifies every
inductive it sees. Log, per corpus, how many predicates and how many data
families have at least one non-root leaf, with leaf and survivor counts. The
second review expects predicates with constructor-headed patterns (typing
and evaluation judgments, `le`, `Forall2`, permutations) to outnumber
indexed data families, and did not count them. The order above does not
wait for that count. Predicates come first because they are the simpler
case and reconstruct without `dep: on`; the census says how much stages 4
and 5 are each worth.

**Translation-shape assertions** for `check-extraction-transl.sh`:

* A regular family with two distinct inhabitants of one fiber, then sixteen
  inhabitants of a wide family: one generic inverse, one membership fact per
  inhabitant, and the same pattern rules whatever the number of inhabitants.
* A family's axioms are identical with and without an unrelated extra
  premise, and identical in the minimized problem. `ev`'s rules are present
  whether or not `nat` is among the premises, and a hypothesis's local fact
  whether or not its family is.
* `vec`, `fin`, `ev`, `le` and a two-index predicate: the rules of §9.2, and
  no rule for an omitted leaf.
* No antecedent guard on a covered variable; the solved field's guard in the
  consequent; an uncovered guard retained, on the rule's own variable.
* Local facts for: a canonical-form goal, fields read in a hypothesis,
  projections in the goal, a closed depth-2 index, a dependent pair, an
  impossible fiber, a stuck residual equation, and a hypothesis needing a
  local equality. Controls with no fact: `n : nat`, `l : list A`.
* Two distinct inhabitants may carry different fields. A single inhabitant's
  two projections satisfy the constructor's joint payload.
* An opaque membership consumer, and a junk-model consistency canary that
  pairs an impossible fiber with an unrelated inhabitant.

**Evaluation.** Screen each switch separately via `eval/rebuild-config.sh`
on identical premises, budgets and prover versions: baseline; first-order
constructor typing; guard-free generic inverse; pattern rules, guarded and
guard-free; local facts; rules and facts together. Record translation time,
FOF size, clausified literals and clauses, fresh symbols and arities,
prover-specific gains and losses, the prover status, and common goals
reconstructed by any prover. Report reconstruction separately for goals
whose core contains an indexed data family, with the batch that succeeded
and whether the proof uses `eq_rect_eq`. Use the repeated-occurrence
fixtures to distinguish fixed rule cost from growth per inhabitant.

Decide by reconstructed goals over a frozen list, in three paired rounds. A
goal reconstructed in every round of one arm and in none of the other is a
stable difference. Adopt a change when its stable gains exceed its stable
losses and every loss has been inspected: a loss with a systematic cause
blocks, a loss that is search perturbation is counted. A rule of no loss at
all would reject every real change, because any change of problem text
moves some proofs across the time limit. Problems whose bytes are identical
in both arms are ties without a run. Report the affected goals, those with
at least one differing problem, next to the whole list; a change confined
to indexed families is otherwise lost in noise. Run the consistency lists
also with guard dropping off and every other rule on (§10.1).

Defer the four-prover evaluation until the upstream E status-filter fix is
available in the Hammer revision under test. E 3.5.11 prints
`% SZS status Theorem`; the affected filter accepts `# SZS` and drops that
success before reconstruction. After taking the fix, confirm a known theorem
through Hammer with only E enabled and the initial tactic shortcut disabled.
Require the E success to be recognized and the proof to reconstruct before
starting the four-prover comparison on the uniform setup. With E hidden, the
goals of the 1024-premise data-family suite proved by some prover are 5 of 6
with guarded pattern rules, 5 of 6 with local facts and 6 of 6 with
guard-free pattern rules.
[CoqHammer issue #238](https://github.com/lukaszcz/coqhammer/issues/238)

## 12. Verification status

**Source reading.** The paths identified in §§1–7 were read for the first
version. Line references in §§3–9 were spot-checked against `27b80e8` by the
second review.

**First review**, at `27b80e8`: the current `tagged` behavior, dumps of the
regular `packet` and two-field record examples, hand-specialized copies of
the same problems, and the 40/384 clause comparison of §8. That comparison
is a synthetic clausification measurement.
[Methods and results](reviews/spec-extraction-adversarial-review.md)

**Second review**, at `27b80e8` with Vampire 5.0.1, E 3.5.11, Z3 4.16.0 and
CVC4 1.8: the prover tables behind §§8–9, the clause counts of §9.6, the
end-to-end and direct-tactic reconstruction results of §10.2, the status
observations of §10.3 and the probe of §10.4.
[Tables, probe definitions and hand-written rules](reviews/spec-extraction-adversarial-review-2.md)

**Measured for this revision**, same setup and probe files: guarded pattern
rules with `∀x. Nat(x) → Nat(S x)` added (§9.1, last table row); the
three-layer local fact on the depth-2 `vec` goal and the one-layer fact on
`ev (S⁴ n)` (§9.3); the axiom names in Vampire's and E's
`ContradictoryAxioms` output (§10.3).

**Plan review**, 2026-11-22, at the sources of `ba29cd0` with the same
provers. The pre-implementation evidence of the implementation plan: the
extensionality reproducer against guard dropping (§9.1), the in-place
replacement of the guarded inverse, and the clause counts of an appended
copy. For this revision: dumps of declarations with computed result
indices, and a prototype of the reader of §10.4 on twelve fixtures and on
the existing test suites. The files are under `.agent-files/evidence` of
the `spec-extraction` worktree.

**Limits.** The goals are synthetic and chosen to need inversion, so the
counts say nothing about corpus rates. Every cell is a single run with a
10 s limit and eight jobs in parallel, and cells near the limit are
unstable. Every variant is a hand edit of a `hammer_dump` file that imitates
the shapes of §9. None of this note is implemented. In particular:

* the measured rules lack the consequent guard of a solved field (§9.4);
* the cover algorithm, the matcher, the bounds of §9.5 and translation time
  were not exercised;
* the reader of §10.4 exists as a prototype patch only: shape evidence on
  hand-written fixtures, no prover run, no count of families with computed
  indices in a corpus;
* the argument of §9.1 for guard-free rules is refuted in one setting, a
  selected extensional function equality; how often that setting occurs was
  not measured;
* the reconstruction expectation of stage 0 comes from direct tactic calls;
* acceptance of `ContradictoryAxioms` was read from the code and the prover
  output, with no implementation to run;
* the numeric bounds of §9.5 are initial values, and corpus-wide impact is
  open (§11).
