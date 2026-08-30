import Game.Levels.ArgWorld.ArgWorld_eg.L02_arg

World "ArgWorld_eg"
Level 3

Title "Example 1"

Introduction "
# **Level 3**
Consider the following argument:
* If the tax rate and unemployment rate go up, then there will be a recession.
* If the GDP goes up, then there will not be a recession.
* The GDP and taxes are both going up.
* Therefore, unemployment is not going up.

Let's validate this argument. We use:
* `T` : the tax rate is going up
* `U` : the unemployment is going up
* `G` : the GDP is going up
* `R` : there will be a recession.
>
See how the statement of this level is precisely this argument?
"

set_option pp.parens true

/-- The economic argument in symbols is given below.-/
Statement (T U G R : Prop) (h1: (T ∧ U) → R) (h2: G → ¬ R) (h3: G ∧ T) : ¬ U := by
  obtain nR := h2 h3.left
  rw[Contrapositive] at h1
  obtain this := h1 nR
  rw[Not_and] at this
  rw[← Imp_iff_not_or] at this
  exact this h3.right

Conclusion "😭 To validate this argument with a truth-table would require 16 rows."
