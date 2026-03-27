import Game.Levels.ArgWorld.L03_arg

World "ArgWorld"
Level 4

Title "Test"

Introduction "
### **🤔 Level 4?**
"

set_option pp.parens true

/--
And.intro doc
-/
DefinitionDoc And.intro as "And.intro"

Statement (P Q R: Prop) (h1 : P → R) (h2 : Q → R) : (P ∨ Q) → R := by
  rw[Imp_iff_not_or,Not_or]
  rw[and_or_right]
  rw[← Imp_iff_not_or,← Imp_iff_not_or]
  exact And.intro h1 h2



Conclusion ""

NewDefinition And.intro
NewTheorem Not_or and_or_right
