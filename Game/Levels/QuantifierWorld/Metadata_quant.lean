import Mathlib.Tactic.TypeStar

syntax "exist " term : tactic

macro_rules
  | `(tactic| exist $w) =>
      `(tactic| refine Exists.intro $w ?_)

syntax "use " term : tactic

macro_rules
  | `(tactic| use $w) =>
      `(tactic| refine Exists.intro $w ?_)

theorem Not_forall {u : Type*} {P : u → Prop} : (¬ ∀ {x}, P x) ↔ (∃ x, ¬ P x) := by
  simp

theorem Not_exists {u : Type*} {P : u → Prop} : (¬ ∃ x, P x) ↔ (∀ x, ¬ P x) := by
  simp

theorem Forall_and.{u_1} {v : Sort u_1} {P Q : v → Prop} : (∀ (x : v), P (x : v) ∧ Q x) ↔ ((∀ (x : v), P x) ∧ (∀ (x : v), Q x)) := by
  rw[forall_and]
