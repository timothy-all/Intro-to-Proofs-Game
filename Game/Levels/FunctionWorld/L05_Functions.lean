import Game.Levels.FunctionWorld.L04_Functions


World "FunctionWorld"
Level 5

Title "function"

Introduction "This is the converse of the previous level; it's also true!"

Statement {u: Type*} (f: Rel_on u) (hf: isFunction f) (C: Set u) : C ⊆ invimage f C → image f C ⊆ C  := by
  intro h y hy
  obtain ⟨x,⟨hxc,hxy⟩⟩ := hy
  obtain ⟨z,⟨hzc,hxz⟩⟩ := h hxc
  obtain hyz : y = z := Fun_output_equal f hf x y z hxy hxz
  rw [← hyz] at hzc
  exact hzc



Conclusion "."
