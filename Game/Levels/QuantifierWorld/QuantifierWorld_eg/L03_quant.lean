import Game.Levels.QuantifierWorld.QuantifierWorld_eg.L02_quant

World "QuantifierWorld_eg"
Level 3

Title "Example 3"

Introduction "
## **Level 3**
"

theorem Forall_and.{u_1} {v : Sort u_1} {P Q : v → Prop} : (∀ (x : v), P (x : v) ∧ Q x) ↔ ((∀ (x : v), P x) ∧ (∀ (x : v), Q x)) := by
  rw[forall_and]

Statement {u : Type*} (P : u → u → Prop) : (∀ x, ∀ y, P x y) → (∀ y, ∀ x, P x y) := by
  intro h y x
  exact h x y


Conclusion ""


NewTheorem Forall_and
