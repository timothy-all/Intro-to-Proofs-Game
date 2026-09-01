import Game.Levels.PfWorld.L13_pf

World "PfWorld"
Level 14

Title "Existence and Uniqueness"

Introduction "
# **Level 14: Existence & Uniqueness**
These kinds of statement are **all over** mathematics. Not only do we want to know if certain things exist, but we're especially interested if those things are unique. The logical symbol `∃!` is short-hand for *there exists a unique...*. To be precise, the symbol `∃!` is defined by the following equivalence:
```
(∃! x, P x) ↔ (∃ x, P x ∧ (∀ y, P y → x = y))
```
How do we address such goals in Lean? We use...
### **❯ The `exist!` tactic**
The `exist!` tactic will split your goal into subgoals -- the first goal is the **existence** statement while the second goal is the **uniqueness** statement. A witness to the existential must be provided. 👉 In our case, try
```
exists! 0
```
"

/-- There exists a unique integer $d$ such that for every integer $x$, we have that $dx = 0$.-/
Statement : ∃! (d : ℤ), ∀ (x : ℤ), d * x = 0 := by
  exist! 0
  Hint "We now have two goals. The *Active Goal* is the existence statement, that being, that `0` actually satisfies the predicate `∀ x : ℤ, 0 * x = 0`. Try to clear this goal."
  intro x
  simplify
  Hint "***Magnificent.*** Now we need to prove uniqueness. Give it a try."
  intro y h
  obtain h' := h 1
  rw[← h']
  simplify

Conclusion "### **🥳 Congrats!**
You've beaten Proof Strategy World! Next up: Relation World."

NewTactic exist!
