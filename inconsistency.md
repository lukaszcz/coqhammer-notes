# A Curry/Russell paradox in the guard-free FOL translation

**Context.** 2026-07-27, extraction branch, commit `951862d`. While curating
`consistency-lemmas.txt` for the four previously-uncurated confirmation corpora,
curation of **dependent-stdlib** flagged five lemmas as *refutable from their own
axioms*. They are not benign vacuity (contradictory hypotheses): the translated
**axioms alone are inconsistent**, independently of the conjecture. This note
explains the inconsistency, gives a self-contained way to reproduce it, and
records the root cause and the fix.

**Bottom line (root cause and fix, verified).** The paradox is *possible*
because the FOL translation is untyped and emits definitional equivalences
without type guards (sections 1–4). But it only *occurred* because of a
regression: CoqHammer already has three premise filters
(`filter_program`, `filter_classes`, `filter_hurkens`) whose entire purpose is
to keep exactly these problematic definitions (`Proper`, `complement`, the
Hurkens universe-paradox lemmas) out of the selected premises — and after the
Rocq **`Stdlib` → `Corelib`** library split their hard-coded name prefixes
stopped matching anything, so all three silently became no-ops. Correcting the
prefixes (section 5) restores the intended behaviour and eliminates **both**
inconsistency sources at their intended mechanism. Verified: regenerating the
whole affected slice (Logic + Structures, 6770 problems across 10 premise
counts) with the corrected filters yields **0 inconsistent problems**, down from
the several `ContradictoryAxioms` present before. No global guard knob is
required.

A runnable copy of the minimal reproduction is saved next to this file as
[`inconsistency-repro.p`](inconsistency-repro.p).

---

## 1. Summary

CoqHammer's FOL translation is *untyped*: every Coq application `f a` becomes a
first-order term `happ(f, a)` (`ap` in the repro), and typing is tracked by side
predicates (`$HasType`, `$_type_NNN`) rather than by the logic. Definitions of
constants are emitted as **definitional equivalences**. On the extraction branch
these equivalences are, by default, emitted **without type guards on their
bound variables** — they hold for *every* first-order term.

Two library definitions are enough to turn that into Russell's paradox:

* `Corelib.Classes.Morphisms.Proper A R m := R m m` — a **diagonal**: it feeds
  its argument `m` to the relation `R` twice.
* `Corelib.Classes.RelationClasses.complement A R x y := R x y -> False` — a
  **negation** of a relation.

Because the encoding is untyped and the definitional equivalences are
unguarded, the prover may instantiate `R` with `complement` applied to the
diagonal and then apply the result *to itself*. That yields a term `w` with
`w w  <->  ~ (w w)`, and — together with the sound axiom "`False` is
uninhabited" — derives `$false`.

## 2. The generated axioms

For `Proper`/`complement`, `Hammer_transl` emits (renamed for readability;
`p(X)` means "the Prop-coded object `X` holds", `ap` is `happ`):

```
def_proper     :  proper = lam                               % $_def_Proper
lam_body       :  ! [A,R,M] :  lam_hold(A,R,M) <=> p(ap(ap(R,M),M))
                                                             % $_lam_NN:  lam A R m := R m m
lam_applied    :  ! [A,R,M] :  p(ap(ap(ap(lam,A),R),M)) <=> lam_hold(A,R,M)
                                                             % $adef_lam_NN_$a3
def_complement :  ! [A,R,X,Y] : comp_hold(A,R,X,Y) <=> ( p(ap(ap(R,X),Y)) => p(false) )
                                                             % $_def_complement
comp_applied   :  ! [A,R,X,Y] : p(ap(ap(ap(ap(comp,A),R),X),Y)) <=> comp_hold(A,R,X,Y)
                                                             % $adef_complement_$a4
no_false       :  ~ p(false)                                 % _HAMMER_COQ_FALSE
```

Every `![...]` ranges over **all** first-order terms: there is no
`$HasType(R, relation A)` antecedent restricting `R` to be an actual relation,
nor `$HasType(x, A)` restricting the points. That is the whole bug.

`no_false` is sound on its own — Coq's `False` is uninhabited, so `~ p(false)`
is a faithful axiom. The inconsistency comes purely from the *unguarded*
definitional equivalences.

## 3. Why it is inconsistent (Russell's construction)

Read `p(ap(ap(R, x), y))` as "`x R y`". The definitions collapse to:

* `lam A R m  <->  m` **is `R`-related to itself** (`R m m`), and `proper = lam`,
  so `Proper` *is* the self-relatedness diagonal.
* `comp A R x y  <->  (x R y -> False)`, i.e. with `no_false`, `comp A R x y`
  holds **iff `x R y` does not**.

Now nothing forces `R` to have a type. Instantiate the relation slot with

```
    W  :=  ap(ap(comp, _), ap(lam, _))        % "complement of the diagonal"
```

`W` is simultaneously usable as a relation *and* as a point (untyped). Feeding
`W` to itself, the two equivalences give

```
    p(ap(ap(W, W), W))   <->   comp _ (lam) W W          (comp_applied / def)
                         <->   ~ (W is lam-related to W)  (def_complement + no_false)
                         <->   ~ p(ap(ap(W, W), W))       (lam_body: lam R m <-> R m m)
```

so `P <-> ~P` for `P = p(ap(ap(W,W),W))`, which is `$false`. This is exactly the
Russell set "the set of all `x` such that `x ∉ x`" reflected through the
untyped application. E prover finds it automatically; the last lines of its
proof build precisely the `lam_hold(_, comp(_, lam), comp(_, lam))` self-application
before closing to `$false`.

## 4. Reproduce it

### 4a. Self-contained (no Coq, ~instant)

Run E prover on the six axioms in [`inconsistency-repro.p`](inconsistency-repro.p):

```
eprover --auto --tstp-format inconsistency-repro.p
#  => # SZS status Unsatisfiable         (axioms alone; there is no conjecture)
```

There is no conjecture in the file, so `Unsatisfiable`/`ContradictoryAxioms`
means the axiom set itself is contradictory.

### 4b. From the real translation (shows guarded vs. unguarded)

Dump the actual axiom for `complement` with guards off (the default) and on:

```coq
From Hammer Require Import Hammer.
Require Import Corelib.Classes.RelationClasses.
(* Set Hammer ClosureGuards.   <- toggle this line *)
Hammer_transl "Corelib.Classes.RelationClasses.complement".
```

* **Guards off (default):**
  `![A,R,x,y]: (complement(A,R,x,y) <=> (R x y => False))` — no antecedents.
* **`Set Hammer ClosureGuards`:**
  `![A]: (HasType(A,Type) => ![R]: (HasType(R, relation A) => ![x]: (HasType(x,A) =>
   ![y]: (HasType(y,A) => (complement(A,R,x,y) <=> (R x y => False))))))`.

### 4c. In the confirmation corpus

The original generated problem
`eval/results/confirmation/current/dependent-stdlib/atp-problems/knn-32/Stdlib.Structures.Orders.IsStrOrder.lt_compat.p`
reports `SZS status ContradictoryAxioms` under `eprover --auto` with its real
conjecture untouched.

## 5. The root cause and the fix

### 5a. Proximate cause: the premise filters regressed to no-ops

The toxic definitions never *should* have reached the prover. CoqHammer has
three premise filters, all enabled by default and force-set on for
problem generation (`hammer_main.ml`, the `gen-atp` hook):

| option | intent | prefix it checked (before) |
|---|---|---|
| `filter_program` | drop `Program.*` boilerplate | `Stdlib.Program.` |
| `filter_classes` | drop the typeclass/`Morphisms`/`RelationClasses` machinery | `Stdlib.Classes.` |
| `filter_hurkens` | drop the Hurkens universe-paradox module | `Stdlib.Logic.Hurkens.` |

`filter_classes` is exactly the guard against this paradox: `Proper` and
`complement` live in `Classes.Morphisms` / `Classes.RelationClasses`, and the
filter is meant to keep their definitions out of premise selection entirely.

After the Rocq **`Stdlib` → `Corelib`** reorganisation these definitions are now
emitted under different names — `Corelib.Classes.Morphisms.Proper`,
`Corelib.Classes.RelationClasses.complement`, and the Hurkens lemmas under a
bare `Hurkens.` prefix. The filters' hard-coded `Stdlib.*` prefixes matched
**nothing**, so all three silently degraded to no-ops and the definitions
leaked back into selection. Measured on the generated problems: `Corelib.Classes.`
names appear in every one of the 1743 dependent-stdlib problems; `Stdlib.Program.`
in none; the Hurkens lemmas under the short `Hurkens.` form.

### 5b. The fix: correct the prefixes (surgical, verified)

`is_nontrivial` in `src/plugin/features.ml` now tests each filter against both
the legacy `Stdlib.*` prefix *and* the current `Corelib.*` / bare form, via a
small `begins_with_any` helper. `add_direct_goal_dependencies` was additionally
hardened to return its result from the *filtered* definition list (`ndefs`)
rather than the full `defs`, so a filtered name that the predictor happens to
rank cannot re-enter through the direct-dependency path. With the corrected
filters:

* `Proper` and `complement` are no longer selected, so their definitional
  equivalences (`$_def_Proper`, `$_def_complement`) are never emitted — the
  paradox in sections 1–4 cannot even be stated. (`Proper` may still appear as
  an *opaque constant* referenced in another premise's type, but without its
  unfolding equation it is inert.)
* the Hurkens lemmas are no longer selected, closing section 7's source too.

**Verified end-to-end.** Rebuilding the plugin with the fix and regenerating the
Logic + Structures slice (677 goals × 10 premise counts = 6770 problems):

* `Stdlib.Structures.Orders.IsStrOrder.lt_compat` (a clear Curry core):
  `ContradictoryAxioms` → no contradiction; `$_def_Proper`/`$_def_complement`
  count drops from 1–2 each to **0**.
* `Stdlib.Logic.Hurkens.PropNeqType.paradox`: `ContradictoryAxioms` → `GaveUp`;
  Hurkens premises drop to **0**.
* Full-slice `eprover --auto` scan (2–6 s each): **0 / 6770** report
  `ContradictoryAxioms` or `Unsatisfiable`, and generation reports 0 errors.

This is a surgical premise-selection fix restoring intended behaviour, not a
global change to the shape of every problem. Its cost is the ordinary one for
any premise-selection change: `Corelib.Classes.*` (Proper/Morphisms/
RelationClasses) premises are now excluded from *all* corpora — which is the
filters' documented intent, and was the effective behaviour before the library
split — so success rates shift and must be re-measured with a full grid re-run
(any commit invalidates the grid checkpoints, which pin `commit == HEAD`).

### 5c. Closure guards: a deeper, optional defence (not needed)

The type-guard machinery still exists as a second line of defence.
`emit_definition_equation` (`src/plugin/coq_transl.ml`, ~line 591) takes a
guarded path when `opt_closure_guards` or `opt_lambda_guards` is set, attaching
`$HasType` antecedents to the bound variables of every definitional equivalence;
otherwise it emits them unguarded. Both default **off**. Enabling them would
block the paradox even if a `Proper`/`complement` definition were selected
(section 4b), but it is a *global knob* — it enlarges every definitional axiom in
every problem, with the classic guard soundness/success-rate tradeoff — and the
filter fix in 5b already removes the source, so guards are **not required** here.
They remain available as belt-and-braces if a future untyped self-application is
found among premises the filters legitimately keep.

## 6. Reach and impact

* Measured over the generated problems (knn-32): the toxic combination
  (`Proper`-definition **and** `complement`-definition co-selected in one
  problem) appears in only **5 / 1743** dependent-stdlib problems and
  **1 / 1121** stdlib-regression problems; **0** in stdpp, color-vector,
  external-equations, dependent-slice. stdlib-regression passed its consistency
  check because its curated list happens not to include that one problem.
* The five dependent-stdlib cases: `IsStrOrder.lt_compat`,
  `MSetInterface.Raw2SetsOn.lt_compat`, `OrdersAlt.Update_OT.compare_spec`
  (clear Proper/complement cores), and `WeakFan.WeakFanTheorem`,
  `SetoidList.ForallOrdPairs_inclA` (slower refutations in the same
  setoid/classical area).
* **Success rates are not inflated by this.** When the axioms are inconsistent E
  and Vampire report `ContradictoryAxioms`, a status the confirmation summarizer
  does **not** count as a success (only `Theorem`/`Unsatisfiable` count). So the
  bug is a genuine soundness hole, but it does not add spurious "proved" goals to
  the tallies.

## 7. A second, unrelated source: `Type : Type` and the Hurkens module

A sweep of the curated consistency lemma sets at all ten premise counts turned up
one more inconsistency, with a **different** root cause:
`Stdlib.Logic.Hurkens.PropNeqType.paradox` reports `ContradictoryAxioms` at
nbayes-256 and nbayes-1024 (it passed at knn-32, where curation ran, because the
premises needed to close the derivation were not selected there).

Its conjecture is `~ (Prop = Type)` and the contradiction core is:

```
_HAMMER_COQ_TYPE_TYPE :  cType___$t(cType)      % HasType(Type, Type), i.e. Type : Type
_HAMMER_COQ_FALSE     :  ~ p(false)
Hurkens.TypeNeqSmallType.paradox                % a sibling Hurkens lemma, in scope
```

This is **not** the Curry paradox, but it has the **same proximate cause** as
section 5a: `filter_hurkens` is precisely the filter meant to keep this module
out of premise selection, and it too regressed to a no-op when the Hurkens
lemmas moved to the bare `Hurkens.` prefix. The underlying reason the module is
*toxic* is deeper: the translation deliberately emits `Type : Type`
(`coq_transl.ml:144`, `_HAMMER_COQ_TYPE_TYPE = mk_hastype (Const "Type")
(Const "Type")`) and does not model Coq's universe hierarchy, and
`Coq.Logic.Hurkens` is exactly the standard library's collection of proofs that
such a universe collapse is inconsistent (Hurkens'/Girard's paradox) — so
translating those lemmas into a `Type:Type` FOL reproduces the very
inconsistency they are about. Closure guards do **not** fix this; modelling
universes would, but that is far out of scope.

**The fix is the same as section 5b.** Correcting `filter_hurkens` to match the
bare `Hurkens.` prefix removes the module's lemmas from selection, so the
`Type:Type` axiom is never combined with them and the contradiction cannot be
built. Verified: after the fix, `PropNeqType.paradox` reports `GaveUp` (was
`ContradictoryAxioms`) and carries **0** Hurkens premises. No universe modelling,
and no need to hand-exclude the module — the filter that was always supposed to
handle it now does.

**Reach:** the `Hurkens` module contributes 10 generated problems, all in
dependent-stdlib (0 in the other corpora). At the 2s check timeout only
`PropNeqType.paradox` actually derived the contradiction; the other Hurkens
lemmas timed out (`GaveUp`) but rested on the same unsound `Type:Type` axiom.
Like the Curry cases, this never inflated success tallies (`ContradictoryAxioms`
is not counted as a proof).

## 8. Status

Two independent inconsistency sources in dependent-stdlib, both root-caused,
both narrow (≈5 Curry + ≤10 Hurkens problems, 0 in the other corpora), neither
inflating success tallies (`ContradictoryAxioms` is not counted as a proof) —
and both now **fixed at a single root cause and verified**:

1. **Curry/Russell paradox** (sections 1–6) — unguarded definitional axioms for
   `Proper`/`complement` enable untyped self-application. They only reach the
   prover because `filter_classes` regressed to a no-op after the
   `Stdlib`→`Corelib` split (section 5a).
2. **`Type : Type` universe collapse** (section 7) — the Hurkens module
   weaponises the translation's deliberate universe erasure. It only reaches the
   prover because `filter_hurkens` regressed the same way.

**Fix (done, verified):** correct the three filter prefixes in
`src/plugin/features.ml` to match both `Stdlib.*` and `Corelib.*`/bare names,
and harden `add_direct_goal_dependencies` to respect the filters (section 5b).
Regenerating the affected slice (6770 problems) gives **0 inconsistent**, with
both former paradox cores now consistent under `eprover --auto`. Closure guards
(section 5c) remain an optional deeper defence but are not needed.

**Remaining:** this is a global premise-selection change, so the confirmation
grid must be re-run to re-measure success rates (`Corelib.Classes.*` premises are
now excluded everywhere, as the filter always intended). The five Curry lemmas
that were excluded from dependent-stdlib's consistency canary *as a paradox
workaround* can be reinstated, since they are consistent again.
