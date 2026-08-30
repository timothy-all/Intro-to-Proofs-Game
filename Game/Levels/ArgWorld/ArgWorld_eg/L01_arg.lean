import Game.Levels.ArgWorld
import Game.Levels.ArgWorld.ArgWorld_eg.arg_eg_docs

World "ArgWorld_eg"
Level 1

Title "Constructive Dilemma"

Introduction "
# **Level 1**
This argument is sometimes called the **Constructive Dilemma**. This level is a little tricky with the tools we currently have. To get you going, let's see about rewriting the goal as an implication. 👉 To do so, start out by trying:
```
rw[← Not_not Q]
```
"
/-- This valid argument is called the **Constructive Dilemma**.-/
Statement (P Q R S : Prop) (hPQ : P → Q) (hRS : R → S) (hPorR : P ∨ R) : Q ∨ S := by
  rw[← Not_not Q]
  Hint "**Great**. 👉 Now try:
  ```
  rw[← Imp_iff_not_or]
  ```
  "
  rw[← Imp_iff_not_or]
  Hint "**Perfect**. We can now use `intro` to introduce the assumption `nQ : ¬ Q` into the proof-state. It might be good to convert the assumption `hPR` into an implication in the same way. See if you can't finish from here."
  rw[← Not_not P] at hPorR
  rw[← Imp_iff_not_or] at hPorR
  intro nQ
  rw[Contrapositive] at hPQ
  exact hRS (hPorR (hPQ nQ))

Conclusion ""
