# Second adversarial review: specification extraction for dependent inductive types

*2026-11-20. Reviews `notes/spec_extraction.md` at notes commit `de5f188`
("Share inversion across dependent type guards"), i.e. the design as revised
after the [first review](spec-extraction-adversarial-review.md). Plugin under
test: worktree `spec-extraction` at `27b80e8`, installed in its `_opam` switch.
Provers: Vampire 5.0.1, E 3.5.11, Z3 4.16.0 (`z3_tptp`), CVC4 1.8. No source
file was changed; every "variant" below is a hand edit of a `hammer_dump` file.*

## Verdict

The direction is right and the measurements support it. On small synthetic
goals, a rule specialized to a constructor-headed index pattern, or a ground
one-layer expansion of a local inhabitant, turns 1024-premise problems that no
prover solves in 10 s into problems solved in well under a second.

The design as written would nevertheless capture only part of that gain,
attribute it to the wrong cause, and leave alone the stage where dependent
goals fail today. The main points, most consequential first:

1. **The index guard is the measured bottleneck, and every rule in the design
   keeps it.** Discharging `Nat(S n)` goes through the lifted arrow typing of
   `S`. Adding one redundant axiom `∀x. Nat(x) → Nat(S x)`, or dropping the
   parameter and index guards from the *existing* generic inverse, recovers
   9–10 of 24 prover cells from a baseline of 1. The design's own example rule
   `∀k w. Nat(k) ∧ M(w,S k) → …` proves nothing at index depth 2.
2. **Indexed inductive predicates are outside the stated scope and gain the
   most.** For `ev : nat → Prop` the 1024-premise baseline is 0 of 12 cells and
   a guard-free pattern rule gives 11 of 12, with no reconstruction problem.
3. **The placement table is either/or; the union is better.** Shared rule
   alone 15 of 24, local expansion alone 17, both together 20. The admission
   rule for local expansion ("goal visibly reads fields") excludes three of
   the four goals where it helped.
4. **Reconstruction is the binding constraint for data families.** With
   today's translation the ATPs already prove all 11 probe goals; 3 fail in
   reconstruction and 6 more succeed only through `dep: on`, which sits in the
   last tactic batch and depends on the axiom `Eq_rect_eq.eq_rect_eq`. §10.2
   fixes the 3 failures and is silent on the other 6.
5. **Proofs from an impossible fiber are reported as `ContradictoryAxioms`**
   by Vampire and E, and `invoke_prover` accepts only `SZS status Theorem`.
   The table row "every constructor provably clashes" is therefore invisible
   on two of four provers.
6. **Index patterns that are recursive functions are emitted over a fresh
   symbol** unrelated to the named function. "Retain residual equations"
   (§9.5) is not usable for `vec A (n + m)`-style indices until that is fixed.
7. **TL;DR item 1 and stage 1 describe the current code.** The 40-versus-384
   clause comparison prices a per-occurrence expansion that `27b80e8` does not
   perform for regular families.

Findings 1, 2, 5 and 6 are independent of the specialization machinery and are
cheaper than it. I recommend doing them, and §10.2, first (see "Suggested
order of work").

## What was measured, and what was not

* **Probe goals.** Eleven goals over `packet`, `vec`, `fin`, `app2`/`appf`
  (index `n + m` / opaque `f n m`) and a dependent pair; three goals over
  `ev : nat → Prop`; four goals over families indexed by a recursive or an
  opaque function. Definitions are in Appendix A.
* **End to end.** `hammer` with `SAutoLimit 0`, `ATPLimit 10`,
  `ReconstrLimit 5` on the 11 + 3 goals.
* **Per prover.** `hammer_dump` files (default 1024 premises, about 2600–2800
  formulas; and `Set Hammer Predictions 64`, about 190–290 formulas), run with
  the plugin's command lines and a 10 s limit. CVC4 was given `--tlimit` in
  milliseconds (see "Smaller points").
* **Variants** (Appendix B), all hand-written in TPTP on top of the dump:
  `base` unchanged; `natS` adds `∀x. Nat(x) → Nat(S x)`; `noguard` removes the
  parameter and index guards from the generic inverses of `vec`/`fin`/`ev`;
  `spec` adds one rule per index pattern (`S k`, `O`) with guards as in §9.3;
  `spec_ng` the same rules without parameter and index guards; `speconly` is
  `spec` with the generic inverses removed; `local` adds the one-layer
  consequence of each local inhabitant as a ground existential fact.

Limits of this evidence. The goals are synthetic and chosen to need inversion,
so the tables say nothing about corpus-wide rates. Every cell is a single run
with eight jobs in parallel; cells near the limit are unstable (one Vampire
success is at 9.8 s). A "cell" is one prover on one goal, and
`ContradictoryAxioms` is counted as a found refutation and marked `*`. The
variants imitate the design's shapes; they are not an implementation of it, so
translation time, the matcher and the budgets of §9.2 were not exercised. I
did not prove the `noguard` variants sound (finding 1 says what would be
needed).

## Findings

### 1. The index guard is the bottleneck, and the proposed rules keep it

**What the design says.** Every elimination rule carries the index guard:
`∀j w. D(j) ∧ M(w,j) → E(w,j)` (§8), `∀k w. Nat(k) ∧ M(w,S(k)) → E_succ(w,k)`
(§9.3), "retain the instantiated field guard unless it follows from available
premises" (§9.5), "each specialized rule must retain the premises needed to
derive it" (§10.1).

**Why that is expensive.** §5(a) shows constructor typing in "unfolded form".
What is emitted is the lifted form. For `S` the dump has

    $_typeof_S     $_arrow$t(nat, nat, S)
    $_arrow_N      ∀A B F. $_arrow$t(A,B,F) → ∀x. t(x,A) → t(happ(F,x), B)
    $adef_S        ∀x. happ(S,x) = S$a1(x)
    $tdef_nat      ∀y. nat$t(y) ↔ t(y, nat)

so `nat$t(S$a1(n))` from `nat$t(n)` takes five inferences, through an arrow
axiom that unifies with every arrow-typed constant. The 1024-premise dump of
g10 has 94 `$_arrow_*` axioms, six of them the same generic axiom up to
renaming, and 515 `$adef_*` axioms. The generic inverse applied to
`v : vec A (S n)` needs `D(S n)` before it yields anything.

**Measured.** Six data-family goals on the 1024-premise dumps. Each cell lists
the provers that succeeded within 10 s and their wall time in seconds
(V Vampire, E E, Z Z3, C CVC4).

| variant | g03 | g04 | g05 | g08 | g09 | g10 (depth 2) | cells |
|---|---|---|---|---|---|---|---|
| `base` | – | – | C4.8 | – | – | – | 1 |
| `natS` | E0.1 | E0.2 Z8.6 | C6.4 | V0.2 E0.1 | E5.2 Z9.5 | E0.1 | 9 |
| `noguard` | E0.1 | E0.2 Z7.4 | C5.5 | V0.2 E0.2 | E5.2 Z10.1 | V0.9 E0.1 | 10 |
| `spec` | V0.2 E0.2 | V0.2 E0.3 Z8.2 | V1.0 Z1.4 C1.4 | V0.2 E0.1 Z1.9 C3.1 | V0.1 E5.1 Z3.9 | – | 15 |
| `speconly` | V0.2 E0.1 | V0.2 E0.2 Z6.3 | V1.0 Z1.5 C1.5 | V0.2 E0.2 Z3.0 C2.6 | V0.2 E0.3 Z2.6 | – | 15 |
| `spec_ng` | V0.2 E0.1 | V0.2 E0.2 Z7.4 | V*0.1 Z0.8 C0.9 | V0.2 E0.1 Z3.1 C2.6 | V0.3 E5.2 Z6.7 | V0.7 E0.1 | 17 |
| `local` | V0.2 E0.1 Z3.2 C1.4 | V0.3 Z1.9 C3.1 | V*0.2 Z1.1 C1.4 | V0.2 E0.1 Z1.4 C1.1 | V0.6 Z0.8 C1.3 | – | 17 |
| `spec` + `local` | V0.2 E0.1 Z2.2 C1.4 | V0.2 E0.2 Z1.0 C2.1 | V*0.2 Z0.6 C1.3 | V0.2 E0.1 Z0.9 C0.9 | V0.7 Z1.2 C1.8 | V0.2 E0.2 | 20 |
| `spec_ng` + `local` | V0.2 E0.1 Z2.0 C1.4 | V0.2 E0.1 Z0.9 C1.4 | V*0.1 Z0.6 C1.0 | V0.2 E0.1 Z0.9 C0.9 | V0.7 Z0.9 C1.0 | V0.1 E0.1 | 20 |

Reading it:

* One redundant typing axiom (`natS`) moves the baseline from 1 to 9 cells,
  and from 1 of 6 goals proved by some prover to 6 of 6. It is a consequence
  of axioms already in the problem, so it needs no soundness argument.
* Dropping the guards from the generic inverse (`noguard`) gives 10 cells.
* The specialized rule adds a further 5–7 cells on top of that, mostly for
  Vampire. So specialization is worth something beyond the guard, but less
  than a comparison against `base` suggests.
* With the guard kept, `spec` proves nothing on g10 (`v : vec A 2`): the rule
  at `k := S O` needs `Nat(S O)` again. Without the guard, Vampire and E prove
  it in 0.7 s and 0.1 s.
* Used as a conjecture on the same 1024-premise problem, `nat$t(S$a1(n))`
  alone takes Vampire 0.3 s, Z3 1.4 s and CVC4 2.1 s; E gives up.

The same pattern appears on the 64-premise dumps, where the baseline is not
starved:

| variant (64 premises) | g03 | g04 | g05 | g08 | g09 | g10 | cells |
|---|---|---|---|---|---|---|---|
| `base` | EC | EZC | VE*C | VEC | ZC | VC | 15 |
| `natS` | VEZC | VEZC | VE*C | VEC | VZC | VC | 19 |
| `noguard` | VEZC | VEZC | VE*C | VEC | VZC | VC | 19 |
| `spec` | VEZC | VEZC | V*E*ZC | VEZC | VZC | EZC | 22 |
| `spec_ng` | VEZC | VEZC | V*E*ZC | VEZC | VZC | VEZC | 23 |
| `local` | VEZC | VEZC | V*E*ZC | VEZC | VEZC | VEC | 23 |

E's proof of g03 `base` at 64 premises uses 12 axioms, among them
`$_arrow_230`, `$adef_S`, `$_typeof_S`, `$_inj_S`, `$_discrim_O$S` and the
inversion of `nat`. Vampire's proof of g03 `spec` uses 5: the pattern rule,
`$tdef_A` and three local typings.

**Consequences for the design.**

* §11 stage 3 says "compare this with the generic rule alone". That
  comparison is confounded. It needs two more controls, both far cheaper than
  the proposal: the generic inverse without covered guards, and first-order
  typing axioms for constructors.
* The guards `D(p̄,ī)` in an elimination rule look like the Tier A case of
  `notes/type_guards.md` §3.3: the antecedent `M(w, I p̄ ī)` is a strict atom,
  false whenever a parameter or index is junk, so the guard is covered. The
  design should either adopt that argument for §5(d) and for every rule in
  §9.3, or say why `M` is not strict for regular families. I did not re-prove
  it; the `noguard` rows are therefore conditional on it.
* If the guard must stay, emit the unfolded typing `∀x̄. ⋀G(xⱼ,Aⱼ) → M(c(x̄), …)`
  for constructors, next to the lifted atom. That is the form §5(a) already
  prints.
* The issue is not specific to numerals. Any index that is not a bare local
  constant (`S (n + m)`, `length l`) needs a function typing through the same
  chain before the rule fires.

### 2. Indexed predicates are out of scope by wording and gain the most

The proposal is phrased for data families throughout: "for a regular data
family" (TL;DR 1), "for regular `Set`/`Type` families" (§9.3), and every rule
has a membership atom `M(w,i)`. A `Prop`-sorted indexed predicate has the same
declaration-level inversion and the same index patterns, and no inhabitant
term at all.

For `ev 0`, `ev n → ev (S (S n))` on the 1024-premise dumps:

| variant | p01 `ev (S (S n)) → ev n` | p02 `ev 1 → False` | p03 `ev (S⁴ n) → ev n` | cells |
|---|---|---|---|---|
| `base` | – | – | – | 0 |
| `natS` | V4.8 E5.1 Z5.5 | – | – | 3 |
| `noguard` | V2.4 E0.2 | Z2.2 | V5.1 E7.7 | 5 |
| `spec` (`∀k. Nat(k) → ev(S(S k)) → ev(k)`, `¬ev(S O)`) | V0.3 E0.1 Z1.3 C1.1 | V*0.1 Z0.9 C1.2 | C4.6 | 8 |
| `spec_ng` | V0.2 E0.2 Z1.0 C1.5 | V*0.1 Z0.8 C1.2 | V0.2 E0.2 Z1.4 C2.4 | 11 |

Two things follow. The guard effect of finding 1 is stronger here: at depth 2
(p03) the guarded rule gets 1 cell of 4 and the guard-free rule 4 of 4. And
predicates have none of the reconstruction cost of finding 4: end to end,
today's `hammer` proves and reconstructs all three goals with plain
`hauto … inv: ev` (via the 64-premise slice).

Inductive predicates with constructor-headed index patterns (typing and
evaluation judgments, `le`, `Forall2`, permutations) are far more common in
the evaluation corpus than indexed data families. I did not count them; the
design should, before choosing which case to implement first. The predicate
case is also strictly simpler: no constructor equation, no erased spine, no
mask question (§10.3).

### 3. Shared rule or local fact: the union wins, and the admission rule is too narrow

§9.3 chooses one emission per candidate and adds "once a shared
specialization covers the uses, omit its per-inhabitant copies". On the
1024-premise table the two placements fail on different provers:

* The shared rule serves the saturation provers. E proves g03, g04, g08 and
  g09 with `spec`, and only g03 and g08 with `local`.
* The local fact serves the SMT solvers. On g03, g04, g08 and g09, Z3 and
  CVC4 together prove 8 of 8 cells with `local` and 4 of 8 with `spec`.
* Both together give 20 cells, against 15 and 17.

The cost of emitting both is small. Clausified with E (`--cnf
--no-preprocessing`) for `vec`:

| formula | clauses | literals | Skolem symbols | shape |
|---|---|---|---|---|
| generic inverse | 10 | 50 | 3, arity 3 | every clause has two positive literals |
| `S k` pattern rule | 3 | 12 | 2, arity 3 | Horn |
| local fact for `v : vec A (S n)` | 3 | 3 | 2 constants | ground units |

Against this, the admission condition for local expansion requires "a goal
term that visibly reads fields of this inhabitant", with projections and
matches as the examples, and excludes "a mention of the same record type".
Read literally, only g04 qualifies (`vhd v`, `vtl v` in the goal). g03 and
g08 state a canonical form (`∃x t. v = vcons A n x t`), and g09 reads the
fields in hypotheses, not in the goal. Those three are where `local` took all
four provers from failure to success (g03, g08) or three of four (g09).

Requested changes: admit the local one-layer fact for every asserted local
inhabitant whose matched fiber leaves one or two branches, whatever the goal
looks like; do not withdraw it when a shared rule exists; add canonical-form
and field-in-hypothesis goals to the stage 2 fixtures.

A related point on depth. One layer is not enough for closed indices: on g10
`local` alone proves nothing at 1024 premises, because the Skolem tail
`T : vec A (S O)` needs a rule again. For an index that is a closed
constructor term, local expansion can be iterated with a hard bound given by
the term itself. §9.2 forbids this ("use the atomic membership … at the next
constructor layer") without distinguishing closed from symbolic indices.

I looked for a cost of keeping the generic inverse next to a pattern rule
that it implies (`spec` against `speconly`) and found none on this suite: the
same 15 cells, similar times.

### 4. Reconstruction is where data-family goals fail today

End to end on the eleven data-family goals, with today's translation:

| goal | first ATP success | reconstruction | whole call |
|---|---|---|---|
| g01 `packet n → P n` | CVC4 knn-64 | **fails**, four ATP proofs tried | 6.7 s |
| g02 `v : vec A 0 ⊢ v = vnil A` | CVC4 knn-256 | `hauto lq: on dep: on`, batch 8 | 1.5 s |
| g03 `v : vec A (S n) ⊢ ∃x t. v = vcons A n x t` | CVC4 knn-64 | `hauto lq: on dep: on`, batch 8 | 2.1 s |
| g04 `… ⊢ v = vcons A n (vhd v) (vtl v)` | CVC4 knn-64 | `hauto lq: on dep: on`, batch 8 | 3.4 s |
| g05 `x : fin 0 ⊢ False` | CVC4 nbayes-128 | **fails**, four proofs tried | 6.5 s |
| g06 `h : app2 k ⊢ ∃n m. k = n + m` | CVC4 knn-256 | `srun eauto` (trivial, `n := 0`) | 0.8 s |
| g07 `h : appf k ⊢ ∃n m. k = f n m` | CVC4 knn-64 | **fails**, four proofs tried | 5.9 s |
| g08 `x : fin (S n) ⊢ x = F1 n ∨ ∃y. x = FS n y` | CVC4 knn-64 | `hauto lq: on dep: on`, batch 8 | 2.4 s |
| g09 `vhd v = vhd w → vtl v = vtl w → v = w` | CVC4 knn-64 | `hauto dep: on`, batch 8 | 36.6 s |
| g10 `v : vec A 2 ⊢ ∃x y. v = …` | CVC4 knn-64 | `hauto lq: on dep: on`, batch 8 | 1.9 s |
| g11 `p : dpair nat fin ⊢ ∃a b. p = dp a b` | CVC4 knn-64 | `hauto … inv: dpair` | 0.8 s |

So the ATP side is already 11 of 11, carried almost entirely by the
64-premise CVC4 slice, and the end-to-end result is 8 of 11. Three separate
causes:

* **Clearing (g01, g05, g07).** The core contains `$_typeof_h` and the
  inversion axiom but no dependency that resolves to the hypothesis, so
  `ClearUnused` removes it (`get_tac_args` builds `used_ids` from `info.deps`
  only, `hammer_main.ml:404`). Checked directly: `clear h; hauto inv: packet`
  fails and `hauto inv: packet` takes 0.01 s; `hauto inv: fin` closes g05 and
  `hauto inv: appf` closes g07 once the hypothesis is kept, both without
  axioms. §10.2 fixes exactly this. It is the most valuable item in the
  design, it is independent of every translation change, and it should not
  wait for stage 2.
* **`dep: on` comes last (g02–g04, g08–g10).** Plain `hauto` with `inv: vec`
  or `inv: fin` fails or exceeds 20 s on g02, g03, g04 and g08 (`sauto`
  likewise on g02 and g03); `hauto lq: on dep: on` closes each in under
  0.05 s. The `dep: on` tactics are the last regular batch
  (`hammer_main.ml:732`). In five cases batches 1–7 failed quickly; in g09
  they ran to their limits and the call took 36.6 s. Every new ATP success
  the proposal produces on an indexed data family will queue behind the same
  seven batches. The provenance of §10.2 is what a router needs: if the core
  contains an inversion (generic or specialized) of a family with non-uniform
  indices, try the `dep: on` tactics in the first batch.
* **`dep: on` proofs use an axiom.** `Print Assumptions` on the reconstructed
  g02, g03, g04 and g08 shows `Eqdep.Eq_rect_eq.eq_rect_eq`. For indices with
  decidable equality the axiom is avoidable. The design should state the
  policy, because it is proposing to make this path more frequent.

Two smaller reconstruction obligations for the new axioms:

* `Atp_names.get_inversions` maps the raw suffix of `$_inversion_<name>` to an
  inductive (`atp_names.ml:47`, identity function). A pattern rule must either
  reuse that exact name or be given a suffix that is stripped, as
  `$_typeof_` names already are (`strip_dollar_suffix`, `:42`).
* A specialized core is smaller than a generic one (5 axioms against 12 on
  g03) and no longer mentions `O_S`/`neq_succ_0`. That is good for the tactic,
  but it means the stage 2 and 3 replays must be run against cores produced
  with the new rules, not against today's cores.

### 5. Impossible fibers are reported as `ContradictoryAxioms`

§9.3 row 4 turns "every constructor clashes" into a consequence that is false
under the membership premise. With that rule present the hypotheses alone are
inconsistent, and the two saturation provers say so:

* g05 with any specialization: Vampire prints `% SZS status
  ContradictoryAxioms`, in three of three standalone reruns of `spec` and of
  `spec_ng` and in the table runs of `spec_ng` and `local` (0.1–0.2 s). The
  status depends on which portfolio strategy finishes first: the table run of
  `spec` at 1024 premises reported `Theorem` after 1.0 s. At 64 premises E
  reports `ContradictoryAxioms` on every variant.
* p02 (`ev 1 → False`): the same for Vampire.
* Toy check (`p(c)`, `∀x. ¬p(x)`, any conjecture): Vampire and E report
  `ContradictoryAxioms`; Z3 and CVC4 report `Theorem`.

`invoke_prover` tests `grep -q "SZS status Theorem"` (`provers.ml:204`), so
these runs count as failures. I read that from the code; there is no
implementation to run it against.

This is partly present today: E already reports `ContradictoryAxioms` for
g05 `base` at 64 premises, because discrimination axioms use native negation.
The proposal makes the conjecture-free refutation the shortest one, so
Vampire flips as well (it reports `Theorem` on g05 `base` at 64 premises and
`ContradictoryAxioms` on every specialized variant). In my variants the
empty-fiber rule is written with FOL negation, as discrimination axioms and
the `CEmpty` guard are. Concluding the Coq-level `False` atom instead would
keep the status `Theorem` when the goal is `False`, and not otherwise.

Requested change: accept `ContradictoryAxioms` as success when the problem
contains local hypotheses, and let reconstruction decide. Add it to the
"impossible fiber" fixture of §11 as an end-to-end assertion on Vampire, not
only as a translation-shape assertion.

### 6. Function-valued index patterns are emitted over a fresh symbol

§9.5 relies on residual equations: "preserve stuck equations for the ATP",
"one constructor can solve `n := k` … and still require `f(k) = j`". For an
index pattern that is a transparent recursive function, today's inverse does
not contain that equation. `mk_inversion` reads the constructor type through
`Coq_typing.destruct_type_app` (`coq_transl.ml:758`), which evaluates it;
evaluation unfolds the constant to its `Fix`, and the `Fix` is lifted again
under a fresh name:

    $_inversion_FunIdx.fam:
      ∀i w. T(i) → fam(i,w) →
        ∃x y. T(x) ∧ T(y) ∧ i = $_fix_58(i, x, y) ∧ w = mkfam(x,y)

where the source is `mkfam : ∀x y, fam (g x y)`. The fresh symbol has its own
copy of `g`'s three defining equations and takes the index variable `i`
itself as a spurious context argument. Nothing but induction relates
`$_fix_58(i,x,y)` to `g(x,y)`, which is what every occurrence and every lemma
uses. `app2 : … → app2 (n + m)` gets `i = $_fix_688(i, n, m, n, m)` in the
same way.

Measured on the goal `h : fam k, H : ∀x y. Q (g x y) ⊢ Q k`, 1024 premises:

| problem | Vampire | E | Z3 | CVC4 |
|---|---|---|---|---|
| as emitted | – | – | – | – |
| the fresh symbol replaced by `g(x,y)` by hand in that one axiom | 5.4 s | – | – | 5.4 s |
| control: the same family over an opaque `go` | 6.0 s | – | – | 8.0 s |

The proof of the repaired problem uses `$_inversion_FunIdx.fam`,
`$_typeof_h`, `$_typeof_k` and `H`. The `Prop` analogue is proved in both
versions, but through the induction principle `pfam_sind`, not through
inversion, so it does not test the equation.

This is the generality gap that matters most for dependent types: after
constructor patterns, function-valued indices (`append`, `n + m`,
substitution in typed syntax) are the common case, and they are the case for
which the design has only "retain the residual equation". Fix the emitted
term before stage 1, and add `app2` to the stage 1 fixtures with an assertion
on the symbol that appears in the equation. Until then the "solved-plus-stuck
results" check in §11 tests the wrong term.

### 7. Stage 1 is the current behaviour, and the headline numbers price something else

At `27b80e8`, `guard_leaf` returns the membership atom for `CRegular` and
`CPropSingleton` (`classify_leaf` yields `None`), and `add_def_axioms` emits
one `$_inversion_<ind>` per declaration. TL;DR item 1 and the first sentence
of §9.3 restate that. The 40-versus-384 clause comparison in §9.4 is against
per-occurrence expansion of regular families, which the code does not do. It
is a fair reason not to regress, not a measure of what this proposal adds.

What the proposal adds over the current code is: declaration-level fording of
bare-variable patterns (helps `packet`; does nothing for `vec`/`fin`, whose
patterns are `S n`); local consequences; pattern rules; expansion bounds; and
provenance. The note would be easier to evaluate if §§8–9 were written as
that delta, each item with its own measured effect. The tables above are a
first version of that for two of the items.

### 8. "Collect across the selected problem" has no home, and makes the output non-monotone

§9.3 decides emission from problem-wide facts: "collect candidate
specializations across the selected problem before emitting", "several
occurrences benefit", "keep the number and aggregate size of extra rules
bounded per problem", "once a shared specialization covers the uses, omit its
per-inhabitant copies".

* Axioms are produced per declaration and cached (`Axhash`), then composed.
  A cross-declaration collection pass is a new phase between conversion and
  emission, not a change to `guard_leaf`.
* One `hammer` call translates many problems: each prover slice (64 to 1024
  premises) owns a fresh state (`prepare_atp`, `provers.ml:457`), and
  `minimize` re-translates with only the used dependencies (`:492`). A rule
  admitted because two premises shared a pattern can disappear from the
  minimized problem, or from the 64-premise slice, and the proof with it.
* The admission words are not yet numbers ("small", "bounded", "profitable",
  "warrants the extra quantified formula"), so the cost model of §9.4 cannot
  be reviewed.

The clause counts in finding 3 suggest the counting is unnecessary for the
constructor-pattern case: a pattern rule is three Horn clauses and a local
fact is three units, in problems of 190 to 2800 formulas. Make admission a
function of the family, the index pattern and the inhabitant alone, so that a
premise's contribution does not depend on which other premises were selected.
Keep the decreasing-index condition of §9.4; that one is about search, and
it is local.

## Smaller points

* **Type-headed indices.** `rigid_clash` only fires on term constructors, so
  for a family indexed by `Type` (`expr : Type → Type`) branches survive with
  equations such as `i = nat`, and nothing in the problem separates `nat`
  from `bool`. §9.5 inherits this ("drop a branch only for a certified clash
  of disjoint translated constructors"). Say so in the scope.
* **SMT matching.** §9.4 limits *extra* recursive rules by a decreasing
  index. The generic inverse of an unindexed recursive family is already an
  unbounded source of terms, and stays. The comparison in §9.4's last
  paragraph should include a problem where the pattern rule is present and
  the generic one fires anyway.
* **CVC4 time limit.** `call_cvc4` passes `--tlimit <ATPLimit>`
  (`provers.ml:353`); CVC4 1.8 documents the flag in milliseconds. In
  practice the limit is not enforced at all: `cvc4 --tlimit 10` ran 41 s on
  g03 until my outer timeout killed it. CVC4's budget is therefore whatever
  `htimeout` allows. Harmless, but any evaluation should record that it is so.
* **E.** The status filter of issue #238 still hides E. With E hidden, the
  goals proved by some prover on the 1024-premise table are: `natS` 4 of 6,
  `noguard` 5, `spec` 5, `local` 5, `spec_ng` 6.
* **Line references** in §§3–9 were spot-checked against `27b80e8` and are
  accurate (`mk_inversion` `:754`, `mk_guards` `:830`, `rigid_clash` `:927`,
  `guard_leaf` `:2411`, `add_typing_axiom` `:3073`, `add_inversion_axioms`
  `:3380`, `add_def_axioms` `:3419`).

## Suggested order of work

1. §10.2 provenance, so that `$_typeof_h` in a core keeps `h`; plus the
   `dep: on` routing and an axiom policy (finding 4). The direct tactic
   checks suggest that 8 of 11 becomes 11 of 11 end to end on this suite with
   no translation change; that was not run through `hammer`.
2. Accept `ContradictoryAxioms` (finding 5).
3. Constructor typing in first-order form, or the Tier A argument for
   dropping `D` from §5(d) (finding 1). Evaluate on the corpus; this is the
   control for everything after it.
4. Emit function-valued index patterns over the named function (finding 6).
5. Pattern rules for indexed predicates (finding 2), guard-free if step 3
   allows.
6. Local one-layer facts and pattern rules for data families, emitted
   together, with admission local to the inhabitant (findings 3 and 8).

## Appendix A. Probe definitions

```coq
Parameter P : nat -> Prop.
Inductive packet : nat -> Set := pack : forall n, nat -> nat -> P n -> packet n.
Inductive vec (A : Type) : nat -> Type :=
  vnil : vec A 0 | vcons : forall n, A -> vec A n -> vec A (S n).
Inductive fin : nat -> Set := F1 : forall n, fin (S n) | FS : forall n, fin n -> fin (S n).
Parameter f : nat -> nat -> nat.
Inductive app2 : nat -> Set := mkapp : forall n m, fin n -> fin m -> app2 (n + m).
Inductive appf : nat -> Set := mkappf : forall n m, fin n -> fin m -> appf (f n m).
Definition vhd A n (v : vec A (S n)) : A := match v with vcons _ _ x _ => x end.
Definition vtl A n (v : vec A (S n)) : vec A n := match v with vcons _ _ _ t => t end.
Inductive dpair (A : Type) (B : A -> Type) : Type := dp : forall a : A, B a -> dpair A B.

Inductive ev : nat -> Prop := ev0 : ev 0 | evSS : forall n, ev n -> ev (S (S n)).

Inductive T : Set := a0 | b0 | nd (x y : T).
Fixpoint g (x y : T) : T :=
  match x with a0 => nd y y | b0 => nd y (nd y y) | nd u v => nd (g u y) (g v y) end.
Parameter go : T -> T -> T.
Inductive fam : T -> Set := mkfam : forall x y, fam (g x y).
Inductive famo : T -> Set := mkfamo : forall x y, famo (go x y).
Inductive pfam : T -> Prop := mkpfam : forall x y, pfam (g x y).
Inductive pfamo : T -> Prop := mkpfamo : forall x y, pfamo (go x y).
```

Goals, each after `intros`:

| id | statement |
|---|---|
| g01 | `forall n, packet n -> P n` |
| g02 | `forall A (v : vec A 0), v = vnil A` |
| g03 | `forall A n (v : vec A (S n)), exists x t, v = vcons A n x t` |
| g04 | `forall A n (v : vec A (S n)), v = vcons A n (vhd A n v) (vtl A n v)` |
| g05 | `forall (x : fin 0), False` |
| g06 | `forall k (h : app2 k), exists n m, k = n + m` |
| g07 | `forall k (h : appf k), exists n m, k = f n m` |
| g08 | `forall n (x : fin (S n)), x = F1 n \/ exists y, x = FS n y` |
| g09 | `forall A n (v w : vec A (S n)), vhd A n v = vhd A n w -> vtl A n v = vtl A n w -> v = w` |
| g10 | `forall A (v : vec A 2), exists x y, v = vcons A 1 x (vcons A 0 y (vnil A))` |
| g11 | `forall (p : dpair nat fin), exists a b, p = dp nat fin a b` |
| p01 | `forall n, ev (S (S n)) -> ev n` |
| p02 | `ev 1 -> False` |
| p03 | `forall n, ev (S (S (S (S n)))) -> ev n` |
| fam / famo | `forall k (h : fam k) (Q : T -> Prop), (forall x y, Q (g x y)) -> Q k`, and the same with `famo`/`go`, `pfam`, `pfamo` |

g06 turned out not to need inversion (`n := 0`), so it is reported only in the
end-to-end table. g01, g02, g06, g07 and g11 on the 1024-premise baseline:
g01 V0.1 Z0.6 C0.5; g02 all four; g06 all four; g07 V0.2 C6.3; g11 V3.9.

## Appendix B. Hand-written variants

Symbol names abbreviated; `vec(A,i,w)` is the dump's `cDefs_2evec___24t`,
`t(x,A)` the generic `$HasType`.

    natS      ∀x. nat(x) → nat(S(x))

    spec      ∀A k w. Type(A) → nat(k) → vec(A,S(k),w) →
                ∃x. t(x,A) ∧ ∃u. vec(A,k,u) ∧ w = vcons(A,k,x,u)
              ∀A w. Type(A) → vec(A,O,w) → w = vnil(A)
              ∀k w. nat(k) → fin(S(k),w) → w = F1(k) ∨ ∃y. fin(k,y) ∧ w = FS(k,y)
              ∀w. ¬fin(O,w)
              ∀k. nat(k) → ev(S(S(k))) → ev(k)          ¬ev(S(O))

    spec_ng   the same with Type(A) and nat(k) removed

    noguard   the dump's own $_inversion_Defs.vec / .fin / EvDefs.ev with the
              leading Type(A) and nat(i) antecedents removed

    local     for a local typing  vec(cA, S(k), cv):
                ∃x. cA$t(x) ∧ ∃u. vec(cA,k,u) ∧ cv = vcons(cA,k,x,u)
              for  vec(cA, O, cv):   cv = vnil(cA)
              for  fin(S(k), cx):    cx = F1(k) ∨ ∃y. fin(k,y) ∧ cx = FS(k,y)
              for  fin(O, cx):       $false

Prover commands, with `N = 10`:

    vampire --mode casc -t N --proof tptp --output_axiom_names on F
    eprover -s --cpu-limit=N --auto-schedule -R --print-statistics -p --tstp-format F
    z3_tptp -c -t:N -file:F
    cvc4 --tlimit N000 --dump-unsat-cores-full F

The scripts and dumps were kept in a session scratch directory and are not
part of the notes repository; the definitions, goals and rules above are
enough to regenerate them.
