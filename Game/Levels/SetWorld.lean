import Game.Metadata
import Game.Levels.SetWorld.L01_set
import Game.Levels.SetWorld.L02_set
import Game.Levels.SetWorld.L03_set
import Game.Levels.SetWorld.L04_set
import Game.Levels.SetWorld.L05_set
import Game.Levels.SetWorld.L06_set
import Game.Levels.SetWorld.L07_set
import Game.Levels.SetWorld.L08_set
import Game.Levels.SetWorld.L09_set
import Game.Levels.SetWorld.L10_set
import Game.Levels.SetWorld.L11_set
import Game.Levels.SetWorld.L12_set


World "SetWorld"
Title "Set World"

Introduction "
# **Sets & Set Connectives**
A **set** `A` is a collection of objects of some type `u` that satisfy a **membership predicate**, say `m`. We often write sets by explicitly referring to the membership predicate. We call this **set-builder** notation. Here's how we would write the set of even integers in set-builder notation:
| | | |
|---|:---:|---|
| | ![Set-builder notation illustration](images/set1.png) | |
>
Often we omit the `universe/type` (so the above might look like `{x | ∃ k, x = 2*k}`) if the type of objects in the set is understood. Set **connectives** (like intersection, union, etc) are also defined by *membership predicates*. Let's see how it all works!
"

Image "images/venn1.png"
