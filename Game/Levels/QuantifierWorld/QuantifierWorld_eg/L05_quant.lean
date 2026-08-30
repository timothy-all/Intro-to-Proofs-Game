import Game.Levels.QuantifierWorld.QuantifierWorld_eg.L04_quant

World "QuantifierWorld_eg"
Level 5

Title "Example 5"

Introduction "
# **Level 5**
You can `intro` the hypothesis ***and*** destructure it at the same time! In other words, instead of
```
intro h
obtain ⟨x,y,hP⟩ := h
```
👉 try
```
intro ⟨x,y,hP⟩
```
"

Statement {u : Type*} (P : u → u → Prop) : (∃ x,∃ y, P x y) → (∃ y, ∃ x, P x y) := by
  intro ⟨x,y,hP⟩
  Hint "Woot! What a shortcut!"
  exist y
  exist x
  exact hP

Conclusion "### **💡 Pro-tip**
The `intro` tactic can destructure `∧` hypotheses as well. For example, if our goal is `⊢ (P ∧ Q) → R`, then
```
intro ⟨hP,hQ⟩
```
will turn the goal into `⊢ R` and introduce `hP : P` and `hQ : Q` as assumptions into the proof state.
"
