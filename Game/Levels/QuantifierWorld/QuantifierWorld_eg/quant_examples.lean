import Game.Levels.QuantifierWorld
import Game.Levels.QuantifierWorld.QuantifierWorld_eg.quant_eg_docs


/-Experience with intro, .left .right schemes-/
example {u : Type} (P Q : u → Prop) (h: ∀ x, P x ∧ Q x) : (∀ x, P x) := by
  intro x
  exact (h x).left

/- More experience with intro, .left .right schemes (foral distributes over and)-/
example {u : Type*} {P Q : u → Prop} (h: (∀ x, P x) ∧ (∀ x, Q x)) : ∀ x, P x ∧ Q x := by
  intro x
  exact And.intro (h.left x) (h.right x)

/- Forall commutes with itself, experience with multiple use intro-/
example {u : Type} (P : u → u → Prop) : (∀ x, ∀ y, P x y) → (∀ y, ∀ x, P x y) := by
  intro h y x
  exact h x y

/- rando example with forall-/
example (u : Type) (P R S : u → Prop) (h1 : ∀ x, P (x) → R (x)) (h2 : ∀ x, P (x) ∧ S (x) ) : ∀ x, R (x) ∧ S (x) := by
  intro a
  obtain hPS := h2 a
  obtain hR := h1 a hPS.left
  exact And.intro hR hPS.right

/- Exists commutes with itself, experience with use-/
example {u : Type} (P : u → u → Prop) : (∃ x,∃ y, P x y) → (∃ y, ∃ x, P x y) := by
  intro ⟨x,y,hP⟩
  use y
  use x
  exact hP

/- experience destructuring exists hypothesis-/
example {u : Type} (P Q : u → Prop) (h₁ : ∃ x, P x) (h₂ : ∀ x, ¬ Q x) : ∃ x, P x ∨ Q x := by
  obtain ⟨x,hx⟩ := h₁
  use x
  left
  exact hx

/- Experience with destructuring exists hypothesis-/
example {u : Type} (P Q: u → Prop) (h1: ∃ x, P x) (h2 : ∀ x, Q x) : ∃ x, P x ∧ Q x := by
  obtain ⟨w,h⟩ := h1
  use w
  obtain hQ := h2 w
  exact And.intro h hQ

/- Experience with push_neg -/
example {u : Type} (P Q R : u → Prop) (h1 : (∀ x, P x) → (∃ y, Q y)) (h2 : ∀ y, ¬ Q y) (h3 : ∀ x, ¬ P x → R x) : ∃ x, R x := by
  rw[Contrapositive] at h1
  push_neg at h1
  obtain ⟨x,hx⟩ := h1 h2
  use x
  exact h3 x hx
