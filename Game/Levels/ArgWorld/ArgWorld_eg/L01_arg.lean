import Game.Levels.ArgWorld
import Game.Levels.ArgWorld.ArgWorld_eg.arg_eg_docs

World "ArgWorld_eg"
Level 1

Title "Rule of Contradiction"

Introduction "
### **Level 1**
This argument is sometimes called the **Rule of Contradiction**. We've unlocked the law of logic `Or_false` to help with this level. 🔍 Check the new entry in the **Theorems** tab.
"

Statement (P : Prop) (h : ¬ P → False) : P := by
  rw[Imp_iff_not_or] at h
  rw[Not_not] at h
  rw[Or_false] at h
  exact h

Conclusion ""

NewTheorem Or_false
