import Game.Levels.QuantifierWorld.L03_quant

World "QuantifierWorld"
Level 4

Title "Existential elimination"

Introduction "
# **Level 4**
In this level, we have an assumption that is existentially quantified. In order to use that assumption, we need to use the principle of **Existential elimination**. Specifically, if we know that `∃ x, P x`, then we can deduce that there must be some specific element `a` of type `u` such that `P a` is true. In order to *obtain* such a witness we use ...
### ❯ The `obtain` tactic ... again
To grab a witness of an existential assumption, we use the `obtain` tactic with some extra syntax. In our case, 👉 try:
```
obtain ⟨a, ha⟩ := h₂
```
The `a` is our witness, the `ha` is the proof that `P a`.
"

/-- We *destructure* our exisntential assumption using *Existential elimination*.-/
Statement {u : Type} (P Q : u → Prop) (h₁ : ∀ x, P x → Q x) (h₂ : ∃ x, P x) : ∃ x, Q x := by
  obtain ⟨a,ha⟩ := h₂
  Hint "See how we now have that `a : u` is a generic object, and `ha : P a` is an assumption? We now need to supply a witness to our existential goal..."
  use a
  Hint "You're on the right track. In fact, you can one-shot it from here."
  exact h₁ a ha

Conclusion "🔧 The `obtain` tactic is a real multi-purpose tool! We'll see more uses for `obtain` going forward. In terms of translating Lean into a human-readable proof, it makes sense to translate a statement like `obtain ⟨a, ha⟩ := h₂` in this proof into *Let $a$ be an element such that $P a$ is true; we know such an element exists from the assumption $h_2$.*"
