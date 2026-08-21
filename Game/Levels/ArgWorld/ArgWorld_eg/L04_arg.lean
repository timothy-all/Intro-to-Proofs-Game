import Game.Levels.ArgWorld.ArgWorld_eg.L03_arg

World "ArgWorld_eg"
Level 4

Title "Example 2"

Introduction "
# **Level 4**
Consider the following argument:
* If I dream of electric sheep, then I'm an android.
* If I'm a carbon based, then I'm human.
* I'm not both an android and human.
* Therefore, I either don't dream of electric sheep or I'm not carbon based.

Let's validate this argument. We use:
* `D` : I dream of electric sheep
* `A` : I'm an android
* `H` : I'm human
* `C` : I'm carbon based
See how the statement of this level is precisely this argument?
"

set_option pp.parens true

/-- The Bladerunner argument in symbols is given below.-/
Statement (D A H C : Prop) (h1: D → A) (h2: C → H) (h3: ¬ (A ∧ H)) : ¬ D ∨ ¬ C := by
  rw[Not_and] at h3
  rw[← Imp_iff_not_or] at h3 ⊢
  intro hD
  rw[Contrapositive] at h2
  exact h2 (h3 (h1 hD))

Conclusion ""
