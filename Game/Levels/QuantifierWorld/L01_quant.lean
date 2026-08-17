import Game.Levels.ArgWorld
import Game.Levels.ArgWorld.ArgWorld_eg

World "QuantifierWorld"
Level 1

Title "Example 1"

Introduction "
## **Level 1**
"

Statement {u : Type*} (P : u → Prop) (a : u) : (∀ x, P x) → P a := by
  intro h
  exact h a

Conclusion ""
