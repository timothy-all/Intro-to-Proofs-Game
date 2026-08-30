import Game.Levels.ArgWorld.ArgWorld_eg.L04_arg

World "ArgWorld_eg"
Level 5

Title "Example 3"

Introduction "
# **Level 5**
Consider the following argument:
* Either Colonel Tigh is a cylon, or he's doing his job and the crew hates him.
* If Colonel Tigh is a cylon, then the crew hates him.
* Therefore, even if Colonel Tigh doesn't do his job, then the crew is still going to hate him.

Let's validate this argument. We use:
* `C` : Colonel Tigh is a cylon
* `H` : The crew hates Colonel Tigh
* `J` : Colonel Tigh is doing his job
>
See how the statement of this level is precisely this argument?
"

set_option pp.parens true

/-- The Battlestar Galactica argument in symbols is given below.-/
Statement (C H J : Prop) (h1: C ∨ (J ∧ H)) (h2: C → H) : ¬ J → H := by
  Hint "The contrapositive might be easier to prove here."
  rw[Contrapositive] at ⊢ h2
  rw[Not_not]
  intro nH
  rw[← Not_not C,← Imp_iff_not_or] at h1
  exact (h1 (h2 nH)).left

Conclusion ""
