import Game.Levels.EquivWorld.EquivWorld_eg.L04_equiv

World "EquivWorld_eg"
Level 5

Title "Not and Nand"

Introduction "
### **Level 5**
We introduce a (seemingly) new connective in this level: the `NAND` connective (not-and) denoted `⊼`. Here's how it is defined in Lean:
```
nand_def (P Q : Prop) : P ⊼ Q ↔ ¬ (P ∧ Q)
```
### **⌨ Typesetting-tip**
In order to typeset the symbol `⊼` type `\\barwedge`.
"

set_option pp.parens true

/-- The negated conjunction of $P$ with itself is logically equivalent to $¬ P$.-/
Statement Nand_self (P : Prop) : (P ⊼ P) ↔ ¬ P := by
  rw[nand_def]
  rw[Not_and]
  rw[Or_self]

Conclusion "### **🤔 Food for thought**
The unary operator `¬` can be expressed in terms of `⊼`."
