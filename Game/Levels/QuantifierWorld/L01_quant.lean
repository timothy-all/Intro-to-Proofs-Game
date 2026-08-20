import Game.Levels.ArgWorld
import Game.Levels.ArgWorld.ArgWorld_eg
import Game.Levels.QuantifierWorld.quant_docs
--import Mathlib.Tactic.TypeStar

World "QuantifierWorld"
Level 1

Title "Example 1"

Introduction "
## **Level 1**
"

variable {u : Type}

Statement (P : u → Prop) (a : u) : (∀ x, P x) → P a := by
  intro h
  exact h a

Conclusion ""
