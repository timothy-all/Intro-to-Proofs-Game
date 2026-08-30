import Game.Levels.ArgWorld.L01_arg

World "ArgWorld"
Level 2

Title "Modus Tolens"

Introduction "
# **Level 2**
This valid argument is sometimes referred to as **Modus Tolens**. Of course, we can prove that Modus Tolens is valid by staring at the truth-table serving as the graphic for this world! But let's try to prove it in Lean. To do so, there's a logical equivalence from worlds of yore that will make this problem look more like the last one. In particular, let's *rewrite* the assumption `hPQ : P → Q` using the **Theorem** `Contrapositive`. 👉 To do so, we can use the `at` syntax with the `rw` tactic:
```
rw[Contrapositive] at hPQ
```
"

/-- This valid argument is known as *Modus Tolens*.-/
Statement (P Q : Prop) (hPQ : P → Q) (nQ : ¬ Q) : ¬ P := by
  rw[Contrapositive] at hPQ
  Hint "Great! We now have
  ```
  hPQ : ¬ Q → ¬ P
  ```
  and `hnQ : ¬ Q`. We can now use the tactics `obtain` and `exact` the same way we did in the last level. Or we can take a shortcut...
  "
  exact hPQ nQ


Conclusion " ### **💡 Pro-tip**
The `obtain` tactic is *very* handy especially when you'll need to use the assumption introduced by `obtain` in more intricate ways. But if you find yourself using `obtain` to introduce a hypothesis to only then call the tactic `exact` on that hypothesis, then you probably could have made your work a little shorter.
"
