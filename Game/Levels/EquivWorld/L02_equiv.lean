import Game.Levels.EquivWorld.L01_equiv

World "EquivWorld"
Level 2

Title "Test"

Introduction "
### **🤔 Level 2?**

"

/--
Notnot doc
-/
TheoremDoc Not_not as "Not_not"

/--
Contrapos doc
-/
TheoremDoc Contrapos as "Contrapos"

/--
rw doc -/
TacticDoc rw

Statement Contrapos (P Q : Prop) : (P → Q) ↔ (¬ Q → ¬ P) := by
  rw[← Or_imp, ← Or_imp]
  rw[Not_not,Or_comm]


Conclusion ""

NewTheorem Not_not
NewTactic rw
