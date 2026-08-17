import GameServer

/--
This is half of **DeMorgan's Law**. It says that

$$¬ (P ∨ Q) ↔ (¬ P ∧ ¬ Q)$$

Here's what it looks like in Lean:
```
Not_or (P Q : Prop) : ¬ (P ∨ Q) ↔ (¬ P ∧ ¬ Q)
```
-/
TheoremDoc Not_or as "EQU : Not_or"

/--
This is half of the **Distributive Law**. It says that

$$(P ∨ (Q ∧ R)) ↔ ((P ∨ Q) ∧ (P ∨ R))$$

Here's what it looks like in Lean:
```
Or_and_left (P Q R : Prop) :
  (P ∨ (Q ∧ R)) ↔ ((P ∨ Q) ∧ (P ∨ R))
```
-/
TheoremDoc Or_and_left as "EQU : Or_and_left"


/--
This is half of the **Distributive Law**. It says that

$$(P ∨ (Q ∧ R)) ↔ ((P ∨ Q) ∧ (P ∨ R))$$

Here's what it looks like in Lean:
```
And_or_left (P Q R : Prop) :
  (P ∧ (Q ∨ R)) ↔ ((P ∧ Q) ∨ (P ∧ R))
```
-/
TheoremDoc And_or_left as "EQU : And_or_left"

/-- This is an **Inverse Law**. It says that

$$ P ∨ ¬ P ↔ T₀ $$
where $T₀$ is a tautology. Here's what it looks like in Lean:
```
Or_not_self (P : Prop) : P ∨ ¬ P ↔ True
```
-/
TheoremDoc Or_not_self as "EQU : Or_not_self"

/-- This is an **Inverse Law**. It says that

$$ P ∧ ¬ P ↔ F₀ $$
where $F₀$ is a contradiction. Here's what it looks like in Lean:
```
And_not_self (P : Prop) : P ∧ ¬ P ↔ False
```
-/
TheoremDoc And_not_self as "EQU : And_not_self"


/--This is an **Identity Law**. It says that

$$ P ∧ T₀ ↔ P $$

where $T₀$ is a tautology. Here's what it looks like in Lean:
```
And_true (P : Prop) : P ∧ True ↔ P
```
-/
TheoremDoc And_true as "EQU : And_true"

/--This is an **Identity Law**. It says that

$$ P ∨ F₀ ↔ P $$

where $F₀$ is a contradiction. Here's what it looks like in Lean:
```
Or_false (P : Prop) : P ∨ False ↔ P
```
-/
TheoremDoc Or_false as "EQU : Or_false"


/--This is a **Domination Law**. It says that

$$ P ∨ T₀ ↔ T₀ $$

where $T₀$ is a tautology. Here's what it looks like in Lean:
```
Or_true (P : Prop) : P ∨ True ↔ True
```
-/
TheoremDoc Or_true as "EQU : Or_true"

/--
The negated conjunction of $P$ with itself is logically equivalent to $¬ P$.
-/
TheoremDoc Nand_self as "EQU : Nand_self"

/--
The definition of the **Negated Conjunction** connective, denoted `⊼`. Here's what it looks like in Lean:
```
nand_def (P Q : Prop) : P ⊼ Q ↔ ¬ (P ∧ Q)
```
-/
DefinitionDoc nand_def as "nand_def"

/--
This is an **Idempotent Law**. It says that

$$ P ∨ P ↔ P $$

Here's what it looks like in Lean:
```
Or_self (P : Prop) : (P ∨ P) ↔ P
```
-/
TheoremDoc Or_self as "EQU : Or_self"

/--
The definition of the **if-and-only-if** connective, denoted `↔`. Here's what it looks like in Lean:
```
iff_def {a b : Prop} : ((a ↔ b) ↔ ((a → b) ∧ (b → a)))
```
-/
DefinitionDoc iff_def as "iff_def"

/--
The definition of the **exclusive-or** connective, denoted `⊻`. Here's what it looks like in Lean:
```
xor_def {a b : Prop} : ((a ⊻ b) ↔ ((a ∧ ¬b) ∨ (b ∧ ¬a)))
```
-/
DefinitionDoc xor_def as "xor_def"
