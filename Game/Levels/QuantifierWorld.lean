import Game.Metadata
import Game.Levels.QuantifierWorld.L01_quant
import Game.Levels.QuantifierWorld.L02_quant
import Game.Levels.QuantifierWorld.L03_quant
import Game.Levels.QuantifierWorld.L04_quant
import Game.Levels.QuantifierWorld.L05_quant
import Game.Levels.QuantifierWorld.L06_quant
import Game.Levels.QuantifierWorld.L07_quant

World "QuantifierWorld"
Title "Quantifier World"

Introduction "
# **Predicates & Quantifiers**
A **predicate** is a variable proposition where the variable comes from some universe of discourse. In Lean, we have:
* `P : Prop` meaning that `P` is a proposition
* `P : u → Prop` meaning that `P` is a *predicate* that takes a variable `u` and spits out a proposition.
>
We use **quantifiers** `∀` (forall) and `∃` (exists) to scope predicates into propositions. The quantified statement `∀ x : u, P x` is like a gigantic `∧` statement:
$$
∀ x , P x ↔ ⋀ P x
$$
Similarly, the quantified statement `∃ x : u, P x` is like a gigantic `∨` statement:
$$
∃ x , P x ↔ ⋁ P x
$$
The graphic of this world illustrates a small-scale version of this interpretation.
>
How do we use quantified statements in Lean? This world will help guide us through it.
"

Image "images/quant.png"
