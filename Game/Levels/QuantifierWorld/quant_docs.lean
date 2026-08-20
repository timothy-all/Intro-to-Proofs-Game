import GameServer

/--
The `use` tactic use *use*ful (hehe) for existential goals. Specifically, if the goal is of the form `⊢ ∃ x, p x`, then assuming `y` is a known object in the tactic state we get that
```
use y
```
Will change the goal to `⊢ p y`.
-/
TacticDoc use


/--
The tactic `push_neg` rewrites the goal by pushing negations deeper into an expression. For instance, the goal `¬ ∀ x, ∃ y, x ≤ y` will be transformed by `push_neg` into `∃ x, ∀ y, y < x`.
-/
TacticDoc push_neg
