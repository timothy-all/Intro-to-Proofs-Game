import Game.Levels.FunctionWorld.L04_Functions


World "FunctionWorld"
Level 5

Title "Functions 5"

Introduction "## **Level 5 : Images and inverse images**

This is the converse of the previous level; it's also true! No hints here, you've got this."

/--Suppose $f: A → A$ and $C ⊆ A$. If  $C ⊆ f^{-1}(C)$, then $f(C) ⊆ C$. -/

Statement {u: Type*} (f: Rel_on u) (hf: isFunction f) (C: Set u) : C ⊆ invimage f C → image f C ⊆ C  := by
  intro h y hy
  obtain ⟨x,⟨hxc,hxy⟩⟩ := hy
  obtain ⟨z,⟨hzc,hxz⟩⟩ := h hxc
  obtain hyz : y = z := Fun_output_equal f hf hxy hxz
  rw [← hyz] at hzc
  exact hzc



Conclusion "Lots of important concepts in math can be written in terms of images and inverse images of functions - one of them is the fundamental concept of **continuity** in Calculus! If this sounds interesting, make sure to take MA 366 Real Analysis."
