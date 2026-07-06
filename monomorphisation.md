# Heuristic monomorphisation and type-guard optimization (TODO points 5 and 6)

*Investigation and design notes, 2026-07-05. Sources: `src/plugin/coq_transl.ml`,
`coq_transl_opts.ml`, `coqterms.ml`, `coq_typing.ml`, `tptp_out.ml`, `provers.ml`
(this repo, rocq-9.1 branch); the CoqHammer paper (Czajka & Kaliszyk, JAR 61,
2018), the shallow PTS embedding paper (Czajka, TYPES 2016 post-proceedings,
LIPIcs 97); Blanchette–Böhme–Popescu–Smallbone "Encoding Monomorphic and
Polymorphic Types" (LMCS 2016); Claessen–Lillieström–Smallbone "Sort It Out
with Monotonicity" (CADE 2011); Bobot–Paskevich (FroCoS 2011); Leino–Rümmer
(TACAS 2010); Meng–Paulson (JAR 2008); Desharnais–Vukmirović–Blanchette–Wenzel
"Seventeen Provers Under the Hammer" (ITP 2022); Qian–Clune–Barrett–Avigad
"Lean-auto" (CAV 2025); companion notes `notes/extraction.md` (Letouzey
connection, TODO 7/9). All concrete FOL outputs below were produced with
`Hammer_transl` using the plugin built from this branch (Rocq 9.1).*

## TL;DR

1. **Do monomorphisation at the CIC₀/`Defhash` level, exactly as the TODO
   insists — the literature has since strongly vindicated this choice.** Every
   measured study finds heuristic monomorphisation the single best-performing
   treatment of polymorphism for ATPs: better than every complete polymorphic
   encoding *and better than the ATPs' own native polymorphism* (LMCS 2016 §8;
   ITP 2022: Vampire TF1 2471 vs monomorphised 2608 goals; Lean-auto's Duper
   solves 8.2% without its monomorphising front-end vs 36.9% with it).
   Monomorphisation is inherently incomplete — a finite equisatisfiable
   instance set always exists by compactness but is not computable
   (Bobot–Paskevich, Thm. 1) — so it is *bounded and heuristic by design*, which
   is acceptable in a hammer because reconstruction re-proves from premises
   anyway. The proven algorithm shape (Sledgehammer, Lean-auto): seed with
   ground "constant instances" from the goal, saturate by matching against
   polymorphic premises, bound by ~3 rounds and ~100–200 new instances.

2. **Doing it at CIC₀ level buys three things a FOL-level pass never could:**
   (a) instantiated bodies β-reduce, so higher-order applications `P @ x`
   become real atoms (`lt(O, x)`) — this is what fixes `List.Forall`;
   (b) re-translating an instance re-runs `check_prop`, so instances where a
   `Type` parameter is instantiated by a *proposition* automatically get the
   `F`-encoding — this fixes the "pair used as conjunction / four definitions
   of pair" limitation (JAR §9) as a special case, for free;
   (c) inductive-type instances regenerate *specialized* inversion,
   injectivity and discrimination axioms through the existing machinery.

3. **Type-guard optimization (TODO 6) is the standard `g_σ` "type-indexed
   predicate family" of the literature, and half of it already exists in
   `tptp_out.ml`.** The `tconst_hash`/`_$t` machinery already prints
   `T(x, list nat)` as `list_$t(nat, x)`. The missing steps are: fuse *ground*
   arguments into the symbol (`list_nat(x)`), generalize head-only
   specialization to whole *type shapes* with abstracted free variables
   (`T(y, list (Q x))` → `list_Q(x, y)`, answering the TODO's question
   directly), and elide the bridge axioms to the generic `t` when no
   type-variable guard survives — after successful monomorphisation the
   generic `t` and all type-as-term traffic disappear from the problem.

4. **A third, optional phase — monotonicity-based guard *erasure* — has
   precise known soundness conditions** (guard a universal variable only if
   its type is possibly finite *and* the variable occurs naked in a positive
   equation; infinite types need no guards at all). This is the principled
   generalization of the current ad-hoc closure-guard omission and of TODO
   point 3, and the PTS paper already flags it as the open question. It is
   separable and should come last.

5. Suggested order: **Phase G first** (guard specialization; small,
   self-contained, benefits every problem immediately), then **Phase M**
   (monomorphisation, the big win), then tuning (keep-generic policy, caps),
   then **Phase E** (erasure) if the evaluation justifies it. Each phase is
   independently evaluable with `eval/`.

---

## 1. Current state (verified on this branch)

### 1.1 Where guards come from

`make_guard ctx ty x` (`coq_transl.ml:659`) is the single dispatcher: for a
non-`Prod` type it emits `$HasType(x, C(ty))` with the type as a converted
FOL *term*; for a `Prod` type with `opt_type_lifting = true` (default) it
lifts the type to a fresh `$_type_<id>` constant characterized extensionally
by `add_def_eq_type_axiom` (`coq_transl.ml:821`):
`∀v. T(v, $_type_N(ȳ)) ⟺ type_to_guard(ty, v)`. Quantifiers are guarded in
`prop_to_formula` (`:643`) and `convert`'s `Quant` case (`:545`) under the
Prop/Type trichotomy of JAR §5.2; inversion/case machinery uses `mk_guards`
(`:279`). A binder `A : Type` itself gets `T(A, Type)`; an inner `x : A` gets
`T(x, A)` with a *variable* second argument — the polymorphism that
monomorphisation eliminates.

### 1.2 The `Forall` pathology (TODO 5's own example), concretely

`Hammer_transl "Corelib.Lists.ListDef.Forall"` today produces (abridged,
pretty-printed; `@` is the FOL apply operator):

```
$_inversion_Forall:
  ∀A P l. T(A,Type) → T(P, $_type_23(A,P,l)) → T(l, list A) → Forall(A,P,l) →
    l = nil(A)
    ∨ ∃x. T(x,A) ∧ ∃l'. T(l', list A) ∧ (P @ x) ∧ Forall(A,P,l')
                       ∧ l = cons(A,x,l')
$_type_23: ∀A P l v. T(v, $_type_23(A,P,l)) ⟺ (∀z. T(z,A) → T(v @ z, Prop))
```

Three distinct problems:

1. **`P @ x`** — a variable-head application. For the ATP this is genuinely
   higher-order: using the axiom requires reasoning about an unknown predicate
   through the apply operator, and the arity/predicate optimizations cannot
   touch it. This, not the guards per se, is why the axiom is "not very usable".
2. **`$_type_23(A,P,l)`** — the lifted guard type `A → Prop` received *all*
   context variables as arguments (canonical-context hashing in
   `remove_type`), so the guard for `P` mentions `P` and `l` themselves. Pure
   noise.
3. **Type variables as term arguments everywhere** — `A` flows through every
   literal, `nil(A)`, `cons(A,x,l')`, `list A`, inflating terms and destroying
   indexing.

Meanwhile, at an actual *use site* the full instantiation is sitting there
waiting to be picked up. For
`bar := forall l : list nat, Forall (fun x => 0 < x) l -> l = l`
the translation produces

```
$_def_bar: bar ⟺ ∀l. T(l, list nat) → Forall(nat, $_lam_1, l) → l = l
$_lam_1:   ∀v. $_lam_1(v) ⟺ lt(O, v)
```

i.e. the occurrence `Forall(nat, $_lam_1, l)` hands us the ground parameter
pair `(nat, λx. 0<x)` — the type *and* the predicate, both closed.

### 1.3 What already exists of TODO 6

`tptp_out.ml` performs a printing-level specialization: `build_tconst_hash`
(`:152`) records the head constant and arity of every type occurring as the
second argument of `$HasType`, `write_fol_formula` (`:333`) prints
`T(y, c(a₁…aₙ))` as `c_$t(a₁,…,aₙ, y)`, and `write_type_axioms` (`:452`)
emits one bridge per type head:

```
$tdef_c: ∀X₁…Xₙ Y. c_$t(X₁,…,Xₙ,Y) ⟺ t(Y, c(X₁,…,Xₙ))
```

So `T(l, list nat)` already reaches the ATP as `list_$t(nat, l)` (and
`T(n, nat)` as the unary `nat_$t(n)`). What is *not* done: ground arguments
are not fused into the symbol (the ATP still sees `nat` as a term argument
and can paramodulate under it), non-head structure is not specialized
(`T(y, list (Q x))` becomes `list_$t(Q(x), y)` with the type term `Q(x)`
alive inside), guards with variable type heads (`T(x, A)`) fall back to the
generic `t`, and the `$tdef_*` bridges are emitted *unconditionally*, keeping
`t` and the type-as-term representation reachable in every problem.

### 1.4 Where a pass plugs in, and the caching constraint

`write_atp_file` (`provers.ml:385`) does: `reinit (goal :: hyps @ deps)`
(populates `Defhash` lazily with *all* accessible definitions — available for
type lookup), then `retranslate (name :: depnames)` (axioms per
premise-selected definition, memoized in `Axhash` by name), then
`write_problem`. Two consequences:

- A monomorphisation pass fits **between `reinit` and `retranslate`**: it
  inspects the selected set, adds instance `coqdef`s to `Defhash`, and
  returns an extended name list. Because instance names are content-derived
  (digest of the instantiation), `Axhash` memoization keeps working —
  translating the instance is problem-independent even though *discovering*
  it is problem-dependent.
- Rewriting occurrences *inside pre-existing premises* would make their
  axioms problem-dependent and invalidate `Axhash` per-name caching. §3.5
  deals with this (bridges by default, rewriting as a later option).

Available infrastructure: NbE evaluator with δ (via `Defhash`), ι and fix
unfolding (`coq_typing.ml:37`), `destruct_type_app`/`get_type_args`,
`check_prop`/`check_type_target_is_*`; substitution primitives
`dsubst`/`simple_subst`/`subst_params`; α-canonical hash-consing
(`hashing.ml`) for deduplication. Nothing type-instantiation-specific exists
yet; the closest template is the `_$a<n>` arity specialization with its
`$adef_*` bridge axioms — the same "mangled instance symbol + linking axiom"
pattern needed here.

---

## 2. What the literature establishes

Only the load-bearing facts; full citations at the end.

**Monomorphisation wins, despite incompleteness.** LMCS 2016 §8 (E, SPASS,
Vampire, Z3, Alt-Ergo on Isabelle problems): monomorphic monotonicity-based
encodings beat all polymorphic encodings; even the natively-polymorphic
Alt-Ergo did *better on monomorphised input than on the equivalent
polymorphic input* (318 vs 260). ITP 2022 re-confirmed at scale with modern
provers: "Despite being incomplete, monomorphizing encodings outperform the
polymorphism-preserving encodings"; native TF1 in Vampire 4.6 still loses to
monomorphise-then-encode (2471 vs 2495 untyped, 2608 typed). Success rate
correlates strongly with symbol/term size — "clutter (whether type
arguments, tags, or guards) slows down automatic provers." Conclusion for
CoqHammer: do not wait for polymorphic ATP support; it exists and it loses.

**The algorithm is a bounded, goal-seeded saturation.** Sledgehammer
(LMCS §7.1): collect the ground instances of symbols occurring in already
monomorphic formulae (above all the goal); for each polymorphic axiom refine
a substitution set by matching those ground instances against the axiom's
occurrences of the same symbols; new instances feed the next round; keep only
fully ground copies. Bounds: `max_mono_iters = 3`,
`max_new_mono_instances = 100` (validated twice, 2013 and 2022). Rationale
for 3 rounds: the third round already produces `list(list(list b))`; more
depth rarely helps. Why3 (Bobot–Paskevich): same matching idea (`Θ*(F)`,
closure of compatible substitutions), but the polymorphic original is *kept*
(identity substitution) with a complete guarded encoding as a safety net —
and their evaluation shows instantiation-plus-guards vastly outperforms
guards alone ("Grd is remarkably helped by Dis"), at an average premise
blow-up of only ~1.8×.

**Lean-auto is the closest relative — monomorphisation for dependent type
theory.** Its unit of instantiation is not a bare type but a **constant
instance**: a head constant with all of its *dependent* arguments filled in
(`@map A B`, `@Eq (List B)`, and crucially type-class instance arguments
travel inside the head). Saturation is queue-based with one global instance
cap; matching is syntactic-with-fingerprints, confirmed by definitional
equality; whether an argument position counts as "dependent" is recomputed
per partial instantiation. It discards hypotheses that fail a
quasi-monomorphicity check. It monomorphises *before* λ-elimination /
apply-operator introduction — same lesson as LMCS §7.2: each instance then
gets its own arity. Lean-auto explicitly benchmarks itself against
CoqHammer's guard encoding and attributes its output being orders smaller to
monomorphisation absorbing dependent heads into single symbols.

**Guard specialization and erasure have exact conditions.** After
monomorphisation, guards become a family of unary predicates `g_σ(x)` — the
literature's standard form, and precisely TODO 6's `list_nat(x)`. Erasure:
a type that is monotonic needs no guards at all, and *infinite-in-all-models*
implies monotonic (Claessen et al. Thm. 1; LMCS Thm. 54). Infinity is
decided by introspection of datatype declarations (a constructor that is
recursive, or has an argument of an infinite type). For possibly-finite
types the featherweight `g??` rule applies: guard a universal variable
**only if it occurs naked** — directly as one side of a positive equation —
**in that formula**; add one unconditional typing axiom `g_σ(f(X̄))` per
function whose result type is possibly finite, plus an inhabitation witness
where needed. Guarding any superset remains sound (LMCS Rem. 72), so
incremental adoption is safe. The stronger NP-complete guard-detection
calculus bought nothing on hammer-generated problems (LMCS §5.2) — use the
linear naked-variable check.

**The CoqHammer-side soundness frame already anticipates all of this.** The
PTS embedding paper proves the core guarded translation sound
(FOL-provable ⇒ inhabited) for logical proof-irrelevant PTSs, shows the
`Δ_Φ` axioms need *no* context guards (all guarded variables live inside an
atom only ever matched against translations of well-typed terms), conjectures
that all lifted-term free-variable guards can be dropped, and explicitly
poses adapting monotonicity inference to this setting as an open problem —
noting its proofs are constructive while the monotonicity results are
model-theoretic. JAR §5.6 supplies the boundary case: the guard on the free
variables of a case scrutinee is *load-bearing* (`∀x. x = c₀ ∧ F x = c₀`
inconsistency), and guard omission interacts dangerously with translating
`eq` to FOL `=` (functional extensionality). The naked-variable criterion is
exactly the principled generalization of that observation: equality is the
only channel through which an unguarded variable can damage the problem.

**Realizability as the intended model** (see `notes/extraction.md` §5): the
semantic reading of `T(x, τ)` as Letouzey's simulation/realizability
predicate gives a uniform admissibility criterion for all optimizations
below — an optimized axiom set is admissible if it still holds in the
realizability model. Letouzey's *type extraction* `Ê` is the guard calculus
in disguise: positions where `Ê` yields a structured ML-ish type are exactly
where a specialized guard predicate exists; positions where `Ê` degenerates
to the unknown type (`Obj.magic` sites: type-level computation, existential
type components) are exactly where the generic binary `t` must remain.

---

## 3. Phase M: heuristic monomorphisation at CIC₀ level

### 3.1 Instantiable parameters and constant instances

For a constant `c` whose type NbE-normalizes to `Πx₁:α₁…Πxₙ:αₙ. σ`, call
position `i` a **specializable parameter** if

- **(tier 1 — types)** `αᵢ` normalizes to an arity ending in `Set`/`Type`
  (this includes `A : Type` and type constructors `F : Type → Type`), or
- **(tier 2 — closed value parameters)** `xᵢ` is a *parameter of an inductive
  type* (any sort, including `P : A → Prop` in `Forall`) or, more generally,
  a higher-order argument position; tier 2 instances are admitted only for
  **closed** instantiation values.

For inductive types, the specializable parameters are simply the declared
parameters (`params_num`); this uniformly covers `Forall`'s `A` *and* `P` —
no separate higher-order machinery is needed where it matters most, because
inductive parameters already delimit exactly what may be instantiated
without touching the recursive structure.

A **constant instance** is a pair of `c` and a vector assigning closed,
NbE-normal CIC₀ terms to a *prefix-closed subset* of its specializable
parameters (following Lean-auto: partial instances participate in discovery;
only sufficiently instantiated ones are materialized — see 3.4). Values are
compared and hash-consed α-canonically (`hashing.ml`), with an NbE
normalization pass first so that `list nat` and `(fun A => list A) nat`
collapse. Closed λ-values (tier 2) are keyed by their canonical form; at
translation time they lambda-lift to the same `$_lam` constant they would
have lifted to at the use site, so no duplication arises.

Two DTT-specific points, both learned from Lean-auto:

- **Prop instantiation is a feature.** When a `Type`-parameter is
  instantiated by a proposition (`prod P Q` used as conjunction), the
  instance is re-classified by `check_prop` during its own translation, and
  the `F`-encoding applies where the generic definition got the `C`/guard
  encoding. The "four definitions of pair" of JAR §9 are then just four
  instances discovered on demand. No FOL-level pass could do this: the
  Prop/Type trichotomy fires during translation.
- **Positivity restriction.** Only the *outermost universally quantified*
  prefix of a premise statement may be instantiated (instantiation of a
  positive-position ∀ yields a CIC consequence; under negative positions —
  e.g. `(∀A, P A) → Q` — it does not). Same rule as Lean-auto's leading-∀
  instantiation. For definitions and inductives the parameters are leading
  binders by construction, so this only constrains statement instances.

### 3.2 Instance discovery

Inputs: the selected set `S` = goal ∷ hyps ∷ premise names, with `Defhash`
populated. Output: a set of constant instances to materialize.

```
seeds := all constant instances occurring in goal and hyps      (priority 0)
       ∪ all constant instances occurring in premise statements (priority 1)
  where "occurring" = subterms App(Const c, a₁…aₖ) with the arguments at
  specializable positions closed and NbE-normal (normalize, then test
  closedness); collect the maximal prefix of instantiated positions.

work := priority queue of (instance, round) seeded above; known := seeds
rounds r = 1 .. K:
  for each polymorphic definition/premise d in S (and instances created in
  round r-1):
    for each occurrence in d of a constant c with variable arguments at
    specializable positions (variables bound by d's leading prefix):
      for each known instance ι of c:
        θ := match ι's values against the occurrence's argument terms
             (first-order matching modulo NbE; cheap fingerprint test,
              then conversion check)
        θ* := unions of compatible substitutions per d   (Why3's Θ*)
        for each θ in θ*: propose instance d⟨θ⟩ (of a premise: a statement
        instance; of a definition/inductive: a symbol instance)
  scan the bodies/statements of newly created instances for new constant
  instances; add to known/work.
stop when: no new instances, or r = K, or |new instances| ≥ Δ_total,
           or per-constant count ≥ Δ_c.
subsumption: drop an instance if another kept instance of the same constant
             is more general (its values match ours).
```

Recommended defaults, imported from the twice-validated Sledgehammer numbers
and to be tuned on `eval/`: **K = 3, Δ_total = 128, Δ_c = 16**, goal-seeded
instances exempt from Δ_c. Everything found in round 1 from the goal/hyps is
kept before anything premise-derived (the Why3 finding: goal-derived
instantiations carry almost all the value).

Discovery cost is one traversal of the selected statements per round with
hash-indexed instance lookup — negligible next to a 10–20 s ATP budget.

### 3.3 Materializing instances

Instance names: `c⟨digest⟩` where the digest hashes the canonical instance
vector (stable across problems → `Axhash`-cacheable; `strip_suffix`-style
mapping back to `c` for `provers.ml` dependency parsing, cf. §3.6).

- **Plain definitions** `c = t : τ`: instance value
  `simpl (mk_long_app t values)` (β-reduces the instantiated prefix), type
  the corresponding instantiation of `τ`; sort recomputed. Fixpoints work
  through the same path (`Fix` under leading `Lam`s; `simpl` handles the
  redexes; fix-lifting then regenerates the unfolding equations with the
  parameters gone).
- **Inductive types** `I` with `params_num = p`, instantiating the first
  `q ≤ p` parameters: register `IndType(I⟨d⟩, [c₁⟨d⟩; …], p−q)` whose type is
  the instantiated arity, and each constructor `cᵢ⟨d⟩` with
  `subst_params`-instantiated type (the existing parameter-substitution code
  path used by `mk_inversion`). Then `add_def_axioms` produces, *through
  entirely existing code*, the specialized typing, injectivity,
  discrimination and inversion axioms. This is where the big win of TODO 5
  lives — see the worked example in §6.
- **Statement instances** of a premise `L : τ` (sort Prop): register
  `(L⟨d⟩, Const(L⟨d⟩), τθ, SortProp)`; its translation is `F(τθ)` labelled
  `L⟨d⟩`. Inside a *freshly created* instance statement, rewrite occurrences
  `App(c, values…, rest)` to `App(c⟨d'⟩, rest)` for every materialized
  instance — instances are new objects, so this rewriting has no caching
  cost and it is what makes the instance's guards ground and its terms
  type-argument-free.

### 3.4 Which instances to materialize

Materialize an instance only if it is **guard-complete**: every remaining
uninstantiated specializable parameter would still receive a sound generic
guard through the normal translation (always true — the translation is
uniform), *and* it satisfies the analogue of Lean-auto's QMono filter worth
having here: after instantiation and `simpl`, the statement contains no
applied occurrence of an *uninstantiated* higher-order variable that was
introduced by the instantiation itself. In practice: tier-1-complete
instances (all sort-parameters ground) are always materialized; partially
instantiated ones only participate in further discovery rounds. This keeps
the output monomorphic where it counts while avoiding a combinatorial fringe
of half-ground copies.

### 3.5 Keep or drop the generic axioms?

The literature splits: Sledgehammer discards non-ground leftovers entirely;
Why3 keeps the generic formula and reports the combination beats either
alone. The tension: dropping loses genuinely polymorphic reasoning steps
(e.g. a lemma applied at a type variable bound in the goal); keeping costs
clutter, and clutter is measurably expensive.

Recommendation: **keep by default, with a size-based override**
(`opt_mono_keep_generic = true`; drop the generic copy of a premise only
when all its occurrences in the goal/hyps are covered by instances). Two
further reasons to keep, specific to CoqHammer: (a) premise selection
already limits the axiom count, so the marginal clutter is bounded by
Δ_total; (b) the generic axioms are the completeness net that makes the
whole pass *monotone in provability* — the monomorphised problem proves
strictly more than the original in the FOL sense (§5.1). Evaluate both
policies; the ITP 2022 data suggests dropping may win once instances are
good, but that should be earned empirically.

Occurrence rewriting inside *pre-existing* premises (making `cons(nat,x,l)`
into `cons⟨nat⟩(x,l)` in an old premise's axioms) is deferred: it breaks
`Axhash` per-name caching (§1.4). Instead, symbol instances automatically
carry a **bridge equation** produced by their own definitional axiom
(`∀x l. cons⟨nat⟩(x,l) = cons(nat,x,l)` follows from translating the
instance value before `simpl` collapses it; emit it explicitly as
`$_mono_<inst>` — the exact analogue of the `$adef_*` arity bridges). The
bridge lets the ATP connect old-style occurrences to the specialized axioms
at unit cost. A later stage can flip on rewriting with an `Axhash` key
extended by the instance-set digest, trading cache hits for cleaner problems
— measure before committing.

### 3.6 Reconstruction and bookkeeping

`provers.ml` parses used-axiom names to premise names. Instance names strip
to their base constant (one `strip_suffix`-style change), so `atp_info.deps`
recovers the original premises; the instance vector is additionally recorded
and can be passed to the reconstruction tactics later (an instantiated
premise is a *stronger* hint than the bare lemma — `sauto`'s `use:` could
receive `(lemma τ̄)` — but that is TODO-4 territory and not needed for
correctness). `Hammer_transl` should gain a variant that runs the
monomorphisation pass first (`Hammer_mono_transl "name"` or a flag), since
per-definition inspection is how every change here gets debugged.

---

## 4. Phase G: type-guard specialization (TODO 6)

### 4.1 The transformation

A FOL-level pass over the collected axioms in `write_problem` (subsuming
the current `tconst_hash`/`$tdef_*` printing machinery rather than adding to
it). For every guard atom `T(x, τ)`:

- **τ ground** (no free variables after NbE normalization): replace by
  `P⟨τ⟩(x)`, a unary predicate hash-consed on the canonical form of τ.
  `T(l, list nat)` → `list_nat(l)`. Ground *subterms* of τ cease to exist as
  FOL terms.
- **τ open**, with free variables `y₁…yₖ` (in order of first occurrence):
  let the *shape* be τ with its free variables abstracted; replace by
  `P⟨shape⟩(y₁,…,yₖ, x)`. This answers the TODO's question directly and
  uniformly:
  - `T(y, list (Q x))` → `list_Q(x, y)` (shape `λa. list (Q a)`),
  - `T(y, list (Q nat))` → `list_Q_nat(y)` (ground, previous case),
  - the current head-only `c_$t` scheme is the degenerate shape
    `λā. c ā`, so this strictly generalizes it.
- **τ a variable or variable-headed application**: keep the generic
  `t(x, τ)`. After Phase M this residue is exactly the not-monomorphisable
  remainder.
- **Lifted `$_type_N` heads**: treated like any other head — instances of
  their guards specialize by shape; their characterization axioms
  (`add_def_eq_type_axiom`) specialize along. (Separately, `remove_type`
  should take only the free variables *of the type itself* as canonical
  context — fixing the `$_type_23(A,P,l)` noise of §1.2 — which is a
  one-line improvement independent of everything else.)

Shape mining must look inside *nested* ground structure: choose the maximal
specialization, i.e. abstract exactly the free variables and nothing else.
Hash-consing across the whole problem gives each shape one predicate symbol.

### 4.2 Bridges only when needed

Emit the linking axiom

```
$tdef_<shape>: ∀ȳ z. P⟨shape⟩(ȳ, z) ⟺ t(z, shape(ȳ))
```

**only if the generic `t` is still reachable**: some guard with a
variable-headed type survives (then an axiom `t(x, A)` with `A` instantiated
to `shape(ū)` must connect to `P⟨shape⟩`), or the shape's instance occurs as
a genuine term argument somewhere outside guard position. Track both
conditions during the pass (the second is the current `build_tconst_hash`
logic, inverted). When Phase M has fully grounded the problem, no bridge is
emitted, `t` disappears, and with it every type-as-term: this is the point
where the untyped problem finally looks like the monomorphic `g̃`-encoded
problems that win in every benchmark. The unconditional `$tdef_*` axioms of
today become the worst case, not the default.

Interactions: requires `opt_hastype = true` (as now); subsumes
`opt_type_optimization` (which should then be retired); composes with
`opt_multiple_arity_optimization` unchanged, since guard predicates never
enter term position.

### 4.3 Correctness

Phase G with bridges is a **definitional extension**: each `P⟨shape⟩` is
introduced by an explicit equivalence, and every guard atom is rewritten by
that equivalence. Equisatisfiability and inter-derivability of the two
problem forms is immediate, and every FOL proof maps back by unfolding the
definition — so the constructive soundness story of the PTS paper is
untouched in structure.

Without bridges, the two directions need separate one-line arguments:

- *Soundness* (the direction that matters): interpret `P⟨shape⟩(ȳ, x)` in
  the intended (realizability) model as `T(x, shape(ȳ))` is interpreted —
  membership/realizability at that type. Every optimized axiom is then true
  in the model whenever the original was; an ATP refutation is as meaningful
  as before. In proof-theoretic terms, the omitted bridge could only be
  needed by a FOL proof that moves between `t(x, σ)` and `P⟨shape⟩`-atoms —
  impossible when no `t`-atom and no `shape`-term exists in the problem,
  which is precisely the elision condition.
- *No loss of provability*: any proof of the bridged problem that never uses
  a bridge axiom is a proof of the unbridged one; the elision condition
  guarantees bridge axioms are inert (their `t`-side atoms unify with
  nothing else in the problem).

---

## 5. Correctness of Phase M, and Phase E (guard erasure)

### 5.1 Phase M is premise strengthening by derivable consequences

Every materialized instance is the image under the *unchanged* translation
of a CIC₀ statement **derivable from the selected premises**: a statement
instance `L⟨θ⟩` is proved by `L` applied to `θ`'s values; a symbol instance's
definitional axioms are the translation of a definitional unfolding of
`c values…`; an inductive instance's inversion/injectivity/discrimination
axioms are instances of the generic ones (or, equivalently, the axioms the
translation would emit for the isomorphic specialized inductive). So the
monomorphised problem = original problem + translations of derivable facts +
conservative definitional extensions (the fresh symbols with their bridges).
Consequences:

- **Soundness is inherited**, not re-proved: whatever meaningfulness
  invariant the base translation has (truth in the realizability model;
  PTS-style constructive soundness for the core), adding translations of
  derivable statements preserves it. Phase M introduces *no new soundness
  debt* — unlike guard erasure, which strengthens axioms.
- **Universe caveat**: instantiation `A := τ` at the CIC₀ level ignores
  universe constraints (CIC₀ already forgets them, JAR §3). A
  universe-inconsistent instance is possible in principle exactly as
  `T(Type,Type)` already is; reconstruction remains the safety net, and the
  exposure is not increased in kind.
- **Incompleteness is inherent and bounded by design** (Bobot–Paskevich
  Thm. 1); K/Δ are the knobs. With `opt_mono_keep_generic = true` the pass
  is monotone: the FOL problem proves at least everything it proved before.

### 5.2 Phase E: erasing guards, principled version (optional; subsumes TODO 3's spirit)

After Phases M and G, the remaining guards are unary/shape predicates on
quantified variables. The literature's conditions transfer as follows:

- **Infinite types need no guards.** Decide infinity by introspection of the
  inductive declaration (a constructor with a recursive argument, or an
  argument of an already-infinite type; `nat`, `list τ`, … qualify). Erase
  `P⟨τ⟩(x) →` from universal quantifiers over such τ — with one crucial
  *CoqHammer-specific* restriction carried over from JAR §5.6: **never erase
  the guard of a case-scrutinee / inversion disjunction** (the axiom's
  conclusion equates the guarded variable with constructor terms — it is
  naked in a positive equation, which is exactly what the naked-variable
  criterion forbids; the classical theory and the JAR counterexample agree
  here, which is reassuring).
- **Possibly-finite types**: guard only variables that occur naked (one side
  of a positive equation) in that formula (`g??`); keep the per-symbol
  typing axioms (`$_typeof_*` already exist) and add an inhabitation witness
  `∃x. P⟨τ⟩(x)` for possibly-finite τ not inhabited by any symbol in the
  problem.
- **Caveats**, stated honestly: the monotonicity theorems are classical and
  model-theoretic; they justify truth-in-the-intended-model (no false
  theorems for the ATP to find, hence no wasted reconstruction), not the
  constructive proof-reconstruction property of the PTS core — the PTS paper
  poses exactly this adaptation as an open problem. Also `eq`-as-`=` means
  *every* Coq-level equation contributes naked occurrences, so the criterion
  must be computed on the final FOL formulas, where this is automatic.
  Finally, LMCS §7.4's warning applies: background-theory infinity can admit
  ATP proofs using "junk" elements that fail reconstruction — rare, and the
  hammer architecture tolerates it, but it argues for shipping Phase E off
  by default and measuring.

TODO 3's example (`Even(x) → nat(x)` making the `nat` guard redundant) is
the *derivability* variant: the guard is erasable because another antecedent
atom entails it in the intended model (via `Even`'s inversion axiom). That
criterion — erase a guard entailed by the remaining antecedents — is sound
by the same model argument, cheap to approximate (an antecedent atom
`Q(…,x,…)` where `Q` is an inductive predicate whose inversion axiom types
`x`), and worth bundling into Phase E as its second rule.

---

## 6. Worked example: `Forall` end to end

Goal context: `bar : forall l : list nat, Forall (fun x => 0 < x) l -> l = l`.

**Discovery** (round 1, from the goal): constant instance
`Forall⟨nat, λx. 0<x⟩` (both inductive parameters — tier 1 + tier 2 in one
step, since both are parameters of the inductive), plus `list⟨nat⟩`,
`cons⟨nat⟩`, `nil⟨nat⟩`.

**Materialization**: inductive instance `Forall⟨d⟩` with `params_num = 0`,
constructors (after `subst_params` and `simpl`):

```
Forall_nil⟨d⟩  : Forall⟨d⟩ nil⟨nat⟩
Forall_cons⟨d⟩ : ∀x l. 0 < x → Forall⟨d⟩ l → Forall⟨d⟩ (cons⟨nat⟩ x l)
```

Note `P x` has β-reduced to the atom `0 < x` — the `P @ x` problem is gone,
not encoded around.

**Translation of the instance** (existing machinery, nothing new), then
Phase G, produces:

```
Forall_cons⟨d⟩:      ∀x l. nat(x) → list_nat(l) →
                        lt(O,x) → Forall⟨d⟩(l) → Forall⟨d⟩(cons⟨nat⟩(x,l))
$_inversion_Forall⟨d⟩: ∀l. list_nat(l) → Forall⟨d⟩(l) →
                        l = nil⟨nat⟩
                        ∨ ∃x l'. nat(x) ∧ list_nat(l') ∧ lt(O,x)
                               ∧ Forall⟨d⟩(l') ∧ l = cons⟨nat⟩(x,l')
```

versus the current §1.2 axiom: no `T(A,Type)`, no `$_type_23(A,P,l)`, no
apply operator, no type-variable traffic, unary guards, and every symbol
monomorphic so the arity optimization applies fully. With Phase E, the
antecedent guards `nat(x)`/`list_nat(l')` on the infinite types drop as well
(the scrutinee guard `list_nat(l)` on the inversion axiom stays). This is,
symbol for symbol, the axiom shape that a HOL hammer would emit for a
monomorphic `Forall_nat` — the shape the ATPs are engineered around.

If TODO 7's per-constructor split (see `notes/extraction.md`) lands too, the
instance's *function* cousins (e.g. `map⟨nat,bool⟩`) additionally become
oriented unit rewrite rules; the two designs multiply.

---

## 7. Options and defaults

```
opt_monomorphisation           runtime (Set Hammer Monomorphisation), default on after eval
opt_mono_iters                 K, default 3
opt_mono_max_instances         Δ_total, default 128
opt_mono_max_per_const         Δ_c, default 16
opt_mono_tier2                 closed HO/value parameters, default on (it is what fixes Forall)
opt_mono_keep_generic          default true (§3.5); evaluate false
opt_mono_rewrite_occurrences   default false initially (§3.5, caching)
opt_guard_specialization       Phase G, default on (subsumes opt_type_optimization)
opt_guard_erasure              Phase E, default off pending eval
```

Most current options in `coq_transl_opts.ml` are compile-time; at least
`opt_monomorphisation` and `opt_guard_erasure` should be runtime options so
the GSMode strategy schedule can diversify over them, the same way ATP ×
premise-count pairs are diversified today.

## 8. Implementation plan

1. **Phase G** (`tptp_out.ml` + a small shape-collection pass; ~200 lines).
   Self-contained, no semantic risk (definitional extension), improves every
   problem that has parameterised guards today. Also do the `remove_type`
   canonical-context fix. Golden-output tests via `Hammer_transl` in
   `tests/`.
2. **Phase M tier 1+2, inductives and definitions, statement instances,
   bridges, keep-generic** (new `src/plugin/monomorph.ml` operating on
   `Defhash`/`coqterm`, hooked in `provers.ml:write_atp_file`; discovery +
   materialization ≈ 400–600 lines, reusing NbE, `subst_params`, `Hashing`).
   `provers.ml` name-stripping; `Hammer_mono_transl` debug command.
3. **Tuning round**: keep-generic on/off, caps, occurrence rewriting with
   extended `Axhash` keys, per-strategy diversification.
4. **Phase E** behind an option, starting with infinite-type erasure minus
   scrutinee guards, then the naked-variable refinement and the
   inversion-entailment rule (TODO 3).
5. Future, orthogonal: once problems are fully monomorphic, a TF0/SMT-LIB
   typed output mode becomes possible — the single best configuration in
   ITP 2022 (cvc5 on TF0). Large `tptp_out` addition; separate project.

## 9. Evaluation plan

`eval/` harness on the stdlib corpus (and the MathComp `_CoqProject.mathcomp`
setup for the HO-heavy end):

- Ablations: baseline / +G / +G+M / +G+M(drop-generic) / +G+M+rewrite /
  +G+M+E, per ATP (Vampire, E, Z3, CVC4/cvc5).
- Metrics: ATP-provable %, reconstruction %, end-to-end %, problem sizes
  (axiom/symbol counts — LMCS found symbol count the best predictor),
  instance counts and cap-hit rates, wall time of the pass.
- Targeted micro-suite: goals about `Forall`/`Exists`/`map`/`fold` at ground
  types, `pair`-as-conjunction cases, boolean-reflection samples — the
  classes TODO 5 names.
- Watch reconstruction rate specifically for Phase E (junk-element proofs)
  and for tier 2 (instances that reconstruct to the same `sauto` premises
  should be neutral).

## 10. Risks and open questions

- **Instance blow-up on type-class-heavy code** (records-as-classes give
  deep parameter nests). Caps bound it; subsumption and goal-seeding keep the
  useful ones. Lean-auto's experience says the queue-with-global-cap design
  degrades gracefully.
- **Premise selection does not see instances** (it runs before). Fine
  initially — instances inherit selection via their parents. TODO 10's idea
  (rank `list nat` etc. as first-class premise candidates) is the natural
  follow-up once instances exist as objects.
- **`Defhash` growth across problems**: instances accumulate like lifted
  constants do today; `cleanup` already clears everything per hammer run in
  practice. Verify with the minimization loop (`Provers.minimize` calls
  `write_atp_file` repeatedly — instance names being content-stable makes
  this a cache *win*).
- **Non-prenex polymorphism** stays generic (positivity restriction, §3.1).
  Rare in stdlib statements; MathComp's canonical-structure style needs its
  own study (TODO 1) — monomorphisation helps there only jointly with
  boolean reflection work.
- **Universe polymorphism**: CIC₀ erases levels already; instances can be
  level-inconsistent in principle; reconstruction guards the gate. If this
  ever shows up in eval as failed reconstructions, check instances with the
  kernel at materialization time (`Typeops`-level check per instance —
  costs milliseconds, kills the risk).
- **Where exactly to stop specializing shapes** (Phase G) when types contain
  large ground subterms: hash-consing makes symbols cheap, but a shape per
  distinct ground type could in pathological cases mint hundreds of
  predicates. Cap by frequency (specialize shapes occurring ≥ 2 times; leave
  singletons on the `c_$t` path).

## References

- Ł. Czajka, C. Kaliszyk. *Hammer for Coq: Automation for Dependent Type
  Theory.* JAR 61:423–453, 2018. §5.2 (F/G/C), §5.5 (optimizations incl.
  `c_T` specialised guards, arity), §5.6 (guard-omission soundness), §9
  (limitations: Prop/Type polymorphism, HO). doi:10.1007/s10817-018-9458-4
- Ł. Czajka. *A Shallow Embedding of Pure Type Systems into First-Order
  Logic.* TYPES 2016, LIPIcs 97, 9:1–9:39. Soundness of the guarded core;
  `Δ_Φ` guard-freeness; §6 remarks on dropping `𝔸_Γ` and on adapting
  monotonicity inference. doi:10.4230/LIPIcs.TYPES.2016.9
- J. C. Blanchette, S. Böhme, A. Popescu, N. Smallbone. *Encoding Monomorphic
  and Polymorphic Types.* LMCS 12(4:13), 2016. Encodings g/t/g?/g??/t?/t??,
  monotonicity calculus, Sledgehammer monomorphisation algorithm and bounds
  (§5.6, §7.1–7.4), evaluation (§8). https://arxiv.org/abs/1609.08916
- K. Claessen, A. Lillieström, N. Smallbone. *Sort It Out with Monotonicity.*
  CADE-23, LNAI 6803, 2011. Monotone erasure theorem; naked variables;
  NP-complete guard-detection calculus (not needed in practice).
- F. Bobot, A. Paskevich. *Expressing Polymorphic Types in a Many-Sorted
  Language.* FroCoS 2011; extended report inria-00591414. Undecidability of
  complete monomorphisation (Thm. 1); Dis/Tw/Exp-Dec-Grd pipeline; keep-the-
  generic-formula design; evaluation (Dis+Grd ≫ Grd).
- J.-F. Couchot, S. Lescuyer. *Handling Polymorphism in Automated Deduction.*
  CADE-21, 2007. Type protection for interpreted sorts.
- K. R. M. Leino, P. Rümmer. *A Polymorphic Intermediate Verification
  Language.* TACAS 2010. Type-arguments encoding sound only under e-matching
  triggers — not for superposition provers.
- J. Meng, L. C. Paulson. *Translating Higher-Order Clauses to First-Order
  Clauses.* JAR 40(1), 2008. Arity optimization (already implemented here);
  encoding soundness matters more as premise count grows.
- M. Desharnais, P. Vukmirović, J. C. Blanchette, M. Wenzel. *Seventeen
  Provers Under the Hammer.* ITP 2022, LIPIcs 237. Monomorphisation beats
  native TF1/TH1 across all provers; best overall: monomorphise + TF0.
- A. Bhayat, G. Reger. *A Polymorphic Vampire.* IJCAR 2020 (TF1 in Vampire;
  since mainlined per *The Vampire Diary*, CAV 2025).
- Y. Qian, J. Clune, C. Barrett, J. Avigad. *Lean-auto: An Interface between
  Lean 4 and Automated Theorem Provers.* CAV 2025. arXiv:2505.14929.
  Monomorphisation for DTT: constant instances with dependent arguments,
  queue saturation with global cap, QMono filter, def-eq matching with
  fingerprints; explicit comparison to CoqHammer's encoding.
- T. Zhu et al. *Premise Selection for a Lean Hammer.* 2025.
  arXiv:2506.07477 (LeanHammer = premise selection + Lean-auto + Duper).
- Sledgehammer user's guide (`max_mono_iters = 3`,
  `max_new_mono_instances = 100`): https://isabelle.in.tum.de/doc/sledgehammer.pdf
- P. Letouzey. PhD thesis, 2004; *A New Extraction for Coq*, TYPES 2002;
  *Extraction in Coq: an Overview*, CiE 2008. Type extraction `Ê` as guard
  calculus; constructor-parameter pruning; realizability model — see
  `notes/extraction.md` §3, §5 for the detailed mapping.
- This repo: `src/plugin/coq_transl.ml` (`make_guard`, `type_to_guard`,
  `prop_to_formula`, `remove_type`, `add_def_eq_type_axiom`),
  `src/plugin/tptp_out.ml` (`tconst_hash`, `write_type_axioms`),
  `src/plugin/provers.ml` (`write_atp_file`), `src/plugin/coq_typing.ml`
  (NbE), `src/plugin/hashing.ml`; `notes/extraction.md` (TODO 7/9 companion
  design); `TODO.md` points 2, 3, 5, 6, 7, 10.
