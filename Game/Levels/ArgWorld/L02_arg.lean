import Game.Levels.ArgWorld.L01_arg

World "ArgWorld"
Level 2

Title "Modus Tolens"

Introduction "
## **Level 2**
This valid argument is sometimes referred to as **modus tolens**. Let's use a logical equivalence to make this problem look more like the last one. If we wish to *rewrite* a hypothesis, say `hPQ` 😉, using a known logical equivalence from the **Theorems** tab, say `contrapositive` 😉, we can use the syntax:
```
rw[contrapositive] at hPQ
```
"


Statement (P Q : Prop) (hPQ : P → Q) (hnQ : ¬ Q) : ¬ P := by
  rw[contrapositive] at hPQ
  Hint "Great! We now have
  ```
  hPQ : ¬ Q → ¬ P
  ```
  and `hnQ : ¬ Q`. We can now use the tactics `obtain` and `exact` the same way we did in the last level. Or we can take a shortcut! 👉 Try:
  ```
  exact hPQ hnQ
  ```
  "
  exact hPQ hnQ


Conclusion " ### **💡 Pro-tip**
The `obtain` tactic is *very* handy especially when you'll need to use the hypothesis introduced by `obtain` in more intricate ways. But if you find yourself using `obtain` to introduce a hypothesis to only then call the tactic `exact` on that hypothesis, then you probably could have made your work a little shorter like we've done in this level.
"
