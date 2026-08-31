import Game.Levels.PfWorld.L06_pf

World "PfWorld"
Level 7

Title "Lots-o-tactics"

Introduction "
# **Level 7: Not equals empty **
This level will require a mix of tactics/strategies. First, we have an iff-statement. 👉 So let's start by splitting our goals with
```
constructor
```
"

/-- If $A$ is not equal to the empty set, then there exists an element $x$ such that $x ∈ A$ (i.e., $A$ is nonempty).-/
Statement Ne_empty_iff_nonempty {u : Type*} (A : Set u) : A ≠ ∅ ↔ ∃ x, x ∈ A := by
  constructor
  Hint "***Good.*** Our first subgoal is an if-then statement where the hypothesis is a negative. Let's tackle the contrapositive. 👉 Accordingly, try:
  ```
  contrapose
  ```
  "
  contrapose
  Hint "Let's simplify with `Not_exists` and `Not_not`."
  rw[Not_exists]
  rw[Not_not]
  Hint "***Ok.*** Now let's `intro` the hypothesis."
  intro h
  Hint "We have a set-equality to prove. So let's use `set_eq_iff`."
  rw[set_eq_iff]
  Hint "***Great.*** Now, let's intro a generic variable..."
  intro x
  Hint "***...and*** use `constructor` to split the iff. See if you can finish this case from here."
  constructor
  intro hx
  exact h x hx
  intro F
  contradiction
  Hint "***Welcome to the second case!*** This one is fairly quick. First, let's `intro` the right stuff."
  intro ⟨x,hx⟩
  Hint "You might try `by_contra` at this point. See if you can finish from here."
  by_contra F
  rw[F] at hx
  contradiction

Conclusion "
"
