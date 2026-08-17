import GameServer


/--
This helps to define the `∩` set connective. Specifically,
```
A ∩ B = {x | x ∈ A ∧ x ∈ B}
```
So `mem_inter_iff` says specifically that `x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B`. Here's how it looks in Lean:
```
mem_inter_iff
  {α : Type u}
  (x : α)
  (a b : Set α) :
    x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b
```
-/
DefinitionDoc Set.mem_inter_iff as "mem_inter_iff"
