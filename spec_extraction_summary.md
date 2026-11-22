The target is **untyped first-order logic with equality**. The translation separates the **representation** of a value from its **specification**: proof fields disappear from constructor terms, but the propositions they establish remain in formulas.

### 1. Terms, propositions, and guards

- `⟦t⟧` is the **erased term**. A represented constructor retains its informative arguments in their original slots and omits proof arguments.
- `⟨P⟩` is the **formula** translating a Rocq proposition `P`.
- `G(w,A)` is the **guard** asserting that target term `w` inhabits Rocq type `A`. An informative binder `∀ x:A, P` translates to `∀x. G(x,A) → ⟨P⟩`; a proof binder contributes a logical premise rather than a term argument.

For a **regular data family** `I`, membership stays atomic: `G(w,I p i) = HasType(w,⟦I p i⟧)`. It is **not** expanded into constructor cases at every occurrence. Existing special representations remain: an empty data type has guard `⊥`; an enum uses a disjunction of tag, payload, and index conditions; a validated subset is represented by its carrier, so `G(w,{x:A | P x}) = G(w,A) ∧ ⟨P w⟩`.

### 2. The specification extracted from a constructor

Write an inductive declaration and one of its constructors schematically as:

```text
I : ∀ p i, s
c : ∀ p a, I p (t_c(p,a))
```

Here `p` is the tuple of **parameters**, `i` the tuple of **indices**, `a` the constructor’s **fields** (each may depend on earlier fields), and `t_c` its **result indices**.

At a target fiber `I p u`, match `t_c(p,a)` against `u` at the informative index positions. A justified constructor clash rules out `c`. Otherwise matching yields a substitution `σ` for solved fields and residual equations `E`. An undecidable comparison remains an equation; it does not eliminate the constructor.

The **constructor branch** is:

```text
∃ unsolved informative fields.
    guards of informative fields
  ∧ translated propositions of proof fields
  ∧ residual index equations E
  ∧ w = ⟦c p a⟧                         [data families only]
```

Apply `σ` throughout, including in dependent field types. A solved informative field no longer needs a witness, but **its guard remains**, and its solution fills its original constructor slot. A proof field contributes its proposition, not a witness or a constructor argument.

### 3. Where the specification is emitted

| Form | Meaning |
|---|---|
| **Generic inverse** | One per eligible declaration: `∀ p i [w]. K → A → ⋁ branches`. For data, `A` is `HasType(w,⟦I p i⟧)`; for an inductive predicate, it is `⟨I p i⟩`, with no subject `w`. `K` contains the retained outer guards. Simplify this inverse **in place**; never append a second version of it. |
| **Pattern rule** | Specialize the inverse at a constructor-shaped index pattern when matching removes meaningful search. No surviving constructor gives `K → ¬A`. Keep the generic inverse for arbitrary indices. |
| **Local fact** | For an actual hypothesis in a reduced fiber, emit the specialized constructor disjunction as a fact when all required guards are available. Otherwise skip it. Where a full fact is not admitted, a witness-independent conjunct shared by every survivor may be emitted instead. Do not emit both. |

For example, from `ev0 : ev 0` and `evSS : ∀ n, ev n → ev (S (S n))`, specialization at `S(S(k))` eliminates the `ev0` branch and solves `n := k` in the other. With its outer index guard omitted, the rule is **`ev(S(S(k))) → Nat(k) ∧ ev(k)`**. The `Nat(k)` on the right is a recovered field guard, not an antecedent to discard.

### 4. Guard policy and limits

`Hammer InversionGuardOmission` is planned **on by default**. It may omit an outer parameter or index guard when that variable occupies a stable, retained, type-forcing path in the antecedent family atom. Eligibility is **per guard**. It never removes the family atom, a proof payload, or a consequent guard. `ClosureGuards` overrides it. This omission is an ATP heuristic, not an implication valid in every untyped model.

Optional output is bounded, in order: **declaration pattern rules, one-layer local facts, then deeper single-survivor chains**. Reaching a limit leaves the generic inverse or last complete fact intact. The ATP uses these formulas for search; Rocq checks the reconstructed proof of the original goal.
