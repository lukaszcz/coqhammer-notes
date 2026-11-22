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

The result indices are read once, by one **index-term reader** shared by every consumer. It exposes constructor heads and keeps a term that does not reduce to one as the declaration wrote it, over the named function: `S n + m` reads as `S(add(n,m))`, `n + m` as `add(n,m)`, `id n` as `n`. The constructor's own axiom is translated from the same reading, so introduction and elimination state the same index terms.

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
| **Constructor typing** | The introduction direction, in each data constructor's own bundle: `∀ p a. field guards → proof payloads → HasType(⟦c p a⟧, ⟦I p t_c⟧)`, stated directly next to the existing lifted membership. |
| **Generic inverse** | One per eligible declaration: `∀ p i [w]. K → A → ⋁ branches`. For data, `A` is `HasType(w,⟦I p i⟧)`; for an inductive predicate, it is `⟨I p i⟩`, with no subject `w`. `K` contains the retained outer guards. Simplify this inverse **in place**; never append a second version of it. |
| **Pattern rule** | Specialize the inverse at a constructor-shaped index pattern when matching removes meaningful search. No surviving constructor gives `K → ¬A`. A function of the declaration alone. Keep the generic inverse for arbitrary indices. |
| **Local fact** | For a goal hypothesis in a reduced fiber, emit the specialized constructor disjunction as a closed, unconditional fact in the hypothesis's own bundle. It depends on the goal context and the declarations, not on which premises were selected. Where a full fact is not admitted, a witness-independent conjunct present in every survivor may be emitted instead. Do not emit both. |

For example, from `ev0 : ev 0` and `evSS : ∀ n, ev n → ev (S (S n))`, specialization at `S(S(k))` eliminates the `ev0` branch and solves `n := k` in the other. With its outer index guard omitted, the rule is **`ev(S(S(k))) → Nat(k) ∧ ev(k)`**. The `Nat(k)` on the right is a recovered field guard, not an antecedent to discard. With the guard retained, it is stated on the rule's own variable: **`Nat(k) → ev(S(S(k))) → ev(k)`**, never `Nat(S(S(k))) → …`.

### 4. Why a rule may be emitted

A formula is emitted because it translates a statement provable in Rocq from the inductive declaration (for a local fact, from the goal context), at the erased representation the translator uses. Every existing axiom has this basis. A rule need **not** be derivable in first-order logic from the other formulas of the same ATP problem. Hence a family's rules are identical in every problem that contains the family, a hypothesis's local fact is present whenever the hypothesis is, and constructor disjointness and injectivity are used whether or not the index type's own axioms were selected. What remains to check is the **representation**: a rule must use the spines, proof masks and constructor symbols the translator emits for every value it covers.

### 5. Guard policy and limits

`Hammer InversionGuardOmission` is planned **on by default**. It may omit an outer parameter or index guard when that variable occupies a stable, retained, type-forcing path in the antecedent family atom. Eligibility is **per guard**. It never removes the family atom, a proof payload, or a consequent guard. `ClosureGuards` overrides it. This omission is an ATP heuristic, not an implication valid in every untyped model: with a selected function equality proved by extensionality it can make a satisfiable problem inconsistent. That limitation is documented, with the option as the opt-out.

`Hammer ConstructorTyping`, also planned **on by default**, is the sound complement. A retained guard such as `Nat(S(k))` then follows from `Nat(k)` by one Horn clause instead of five inferences through the lifted arrow type, for every guarded premise and not only for inversions.

Optional output is bounded **per declaration and per hypothesis**, never by an allowance shared across a problem, so a rule's presence does not depend on the other premises. There is no cap on the number of pattern leaves: where an index separates the constructors, all leaf rules together are about the size of the generic inverse. Reaching a limit leaves the generic inverse or last complete fact intact. The ATP uses these formulas for search; Rocq checks the reconstructed proof of the original goal.
