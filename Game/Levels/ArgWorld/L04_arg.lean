import Game.Levels.ArgWorld.L03_arg

World "ArgWorld"
Level 4

Title "Test"

Introduction "
## **Level 4**
"

set_option pp.parens true

/--
And.intro doc
-/
DefinitionDoc And.intro as "And.intro"

Statement (P Q R: Prop) (hPR : P → R) (hQR : Q → R) : (P ∨ Q) → R := by
  rw[Imp_iff_not_or,Not_or]
  rw[and_or_right]
  rw[← Imp_iff_not_or,← Imp_iff_not_or]
  exact And.intro hPR hQR



Conclusion ""

NewDefinition And.intro
NewTheorem Not_or and_or_right
