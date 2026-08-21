import Game.Metadata
import Game.Levels.ArgWorld.L01_arg
import Game.Levels.ArgWorld.L02_arg
import Game.Levels.ArgWorld.L03_arg
import Game.Levels.ArgWorld.L04_arg
import Game.Levels.ArgWorld.L05_arg
import Game.Levels.ArgWorld.L06_arg
import Game.Levels.ArgWorld.L07_arg
import Game.Levels.ArgWorld.L08_arg

World "ArgWorld"
Title "Argument World"

Introduction "
# **Arguments**
An **argument** is an implication of the form
```
(h₁ ∧ h₂ ∧ ⋯ ∧ hₙ) → c
```
The propositions `hᵢ` are called **assumptions** (or **hypotheses**), and the proposition `c` is called the **conclusion**. We say that an argument is **valid** to mean that `c` is true whenever the hypotheses `hᵢ` are all true. We say that an argument is **invalid** (or a **fallacy**) to mean that it is not valid. In terms of truth tables, an argument is valid means that any row where all the hypotheses are true will also report that the conclusion is true. The graphic in this world illustrates the valid argument known as *Modus Tolens*.

Much like logical equivalences, the game is aware of some well-known valid arguments.But unlike logical equivalences, these well-known valid arguments are more baked into the *syntax* of Lean itself. For example, suppose we know `h₁ : P → Q` and `h₂ : P`. Then `h₁ (h₂)` is a proof of `Q` -- it's as if `h₁` is a function whose input is `P` (or rather a proof of `P`) and whose output is `Q` (or rather a proof of `Q`).

Whereas the proofs we wrote in Logical Equivalence World all relied on substitution (or the `rw` tactic), our proofs in Argument World will begin to get more delicate. Let's get started!
"


Image "images/arg1.png"
