import Game.Levels.EquivWorld.EquivWorld_eg.L05_equiv

World "EquivWorld_eg"
Level 6

Title "Not and Nand"

Introduction "
# **Level 6: Not and Nand**
We introduce a (seemingly) new connective in this level: the `NAND` connective (not-and) denoted `⊼`. Here's how it is defined in Lean:
```
nand_def (P Q : Prop) : P ⊼ Q ↔ ¬ (P ∧ Q)
```
### **⌨ Typesetting-tip**
In order to typeset the symbol `⊼` type `\\barwedge`.
"

def Nand (P Q : Prop) : Prop := ¬ (P ∧ Q)
infix:70 " ⊼ " => Nand

theorem nand_def (P Q : Prop) : P ⊼ Q ↔ ¬ (P ∧ Q) := Iff.rfl

set_option pp.parens true

/-- The negated conjunction of $P$ with itself is logically equivalent to $¬ P$.-/
Statement Nand_self (P : Prop) : (P ⊼ P) ↔ ¬ P := by
  rw[nand_def]
  rw[Not_and]
  rw[Or_self]

Conclusion "### **🤔 Food for thought**
The unary operator `¬` can be expressed in terms of `⊼`."

NewDefinition nand_def
NewTheorem Or_self And_self
