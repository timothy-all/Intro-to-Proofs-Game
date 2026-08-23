import Game.Levels.QuantifierWorld
import Game.Levels.QuantifierWorld.QuantifierWorld_eg.quant_eg_docs

World "QuantifierWorld_eg"
Level 1

Title "Example 1"

Introduction "
# **Level 1**
![test](images/pic0.png)
"

Statement {u : Type*} (P Q : u → Prop) (h: ∀ x, P x ∧ Q x) : (∀ x, P x) := by
  intro x
  exact (h x).left

Conclusion ""
