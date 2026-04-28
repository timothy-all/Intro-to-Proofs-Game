import GameServer

/--
This is an **Identity Law**. It says that

$$ P ∨ F₀ ↔ P $$

where $F₀$ is a contradiction. Here's what it looks like in Lean:
```
Or_false (P : Prop) : P ∨ False ↔ P
```
-/
TheoremDoc Or_false as "Or_false"
