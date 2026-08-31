import Game.Levels.RelationWorld.L01_Cartesianproducts
import Game.Levels.RelationWorld.L02_Cartesianproducts
import Game.Levels.RelationWorld.L03_Relations
import Game.Levels.RelationWorld.L04_Relations
import Game.Levels.RelationWorld.L05_Relations
import Game.Levels.RelationWorld.L06_Relations
import Game.Levels.RelationWorld.L07_Relations
import Game.Levels.RelationWorld.L08_Relations
import Game.Levels.RelationWorld.L09_OrderRelations
import Game.Levels.RelationWorld.L10_OrderRelations
import Game.Levels.RelationWorld.L11_OrderRelations
import Game.Levels.RelationWorld.L12_EquivRelations
import Game.Levels.RelationWorld.L13_EquivRelations
import Game.Levels.RelationWorld.L14_EquivRelations
import Game.Levels.RelationWorld.L15_EquivRelations
import Game.Levels.RelationWorld.L16_EquivRelations



World "RelationWorld"
Title "Relation World"

Introduction "
## **Relation World**

A relation from `A` to `B` is a set containing ordered pairs of the form `(a,b)` with `a` coming from `A` and `b` coming from `B`. This is an extremely general concept that has, as special cases, several fundamental mathematical ideas: partial orders (relations like ≤, for instance), equivalence relations (modular arithmetic, for instance), and functions. In this world, we'll first spend a couple levels working with ordered pairs to get used to how they work in Lean, then we'll start working with proofs involving relations.

# **💡 Pro-tip**

Keep an eye out for the difference between *types* (the logical foundation Lean is built in) and *sets* (the logical foundation typically used for mathematics). Much of Relation World is written using types because the way the work is sometimes indistinguishable from sets & makes the proofs smoother, but sets make an important appearance too!
"

Image "images/relworld.png"
