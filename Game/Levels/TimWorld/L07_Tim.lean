import Game.Levels.TimWorld.L06_Tim

World "TimWorld"
Level 7

Title "Test"

Introduction "
### **🤔 Level 7?**
"

set_option pp.parens true

/--
And.intro doc
-/
DefinitionDoc And.intro as "And.intro"

Statement (P Q R: Prop) (h1 : P → R) (h2 : Q → R) : (P ∨ Q) → R := by
  rw[← Or_imp,Not_or]
  rw[and_or_right]
  rw[Or_imp,Or_imp]
  exact And.intro h1 h2



Conclusion ""

NewDefinition And.intro
