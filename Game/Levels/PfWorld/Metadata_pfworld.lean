import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Ring

def Divides (x y : Int) := ∃ z, x * z = y

def isEven (x : Int) := ∃ k, x = 2 * k

def isOdd (x : Int) := ∃ k, x = 2 * k + 1

syntax "simplify" : tactic
macro_rules
| `(tactic| simplify) => `(tactic| push_cast; ring)


syntax "exist! " term : tactic
macro_rules
  | `(tactic| exist! $w) =>
      `(tactic| refine Exists.intro $w ?_; dsimp; refine ⟨?exist,?uniq⟩)
