import GameServer


/--
This is half of the **Distributive Law**. It says that

$$(P ∨ (Q ∧ R)) ↔ ((P ∨ Q) ∧ (P ∨ R))$$

We can prove the **Distributive Law** with a truth-table:
$$
\begin{array}{|ccc||cc|}
  \hline
  P & Q & R & P ∨ (Q ∧ R) & (P ∨ Q) ∧ (P ∨ R)  ) \\
  \hline
  T & T & T & T & T \\
  T & T & F & T & T \\
  T & F & T & T & T \\
  T & F & F & T & T \\
  F & T & T & T & T \\
  F & T & F & F & F \\
  F & F & T & F & F \\
  F & F & F & F & F \\
  \hline
\end{array}
$$
-/
TheoremDoc Or_and_left as "EQU: Or_and_left"


/--
This is half of the **Distributive Law**. It says that

$$(P ∧ (Q ∨ R)) ↔ ((P ∧ Q) ∨ (P ∧ R))$$

We can prove the **Distributive Law** with a truth-table:
$$
\begin{array}{|ccc||cc|}
  \hline
  P & Q & R & P ∧ (Q ∨ R) & (P ∧ Q) ∨ (P ∧ R)  ) \\
  \hline
  T & T & T & T & T \\
  T & T & F & T & T \\
  T & F & T & T & T \\
  T & F & F & F & F \\
  F & T & T & F & F \\
  F & T & F & F & F \\
  F & F & T & F & F \\
  F & F & F & F & F \\
  \hline
\end{array}
$$
-/
TheoremDoc And_or_left as "EQU: And_or_left"

/-- This is an **Inverse Law**. It says that

$$ P ∨ ¬ P ↔ T₀ $$

where $T₀$ is a tautology. We can prove the **Inverse Law** with a truth-table
$$
\begin{array}{|cc||c|}
  \hline
  P & ¬ P & P ∨ ¬ P \\
  \hline
  T & F & T \\
  F & T & T \\
  \hline
\end{array}
$$
-/
TheoremDoc Or_not_self as "EQU: Or_not_self"

/-- This is an **Inverse Law**. It says that

$$ P ∧ ¬ P ↔ F₀ $$

where $F₀$ is a contradiction. We can prove the **Inverse Law** with a truth-table
$$
\begin{array}{|cc||c|}
  \hline
  P & ¬ P & P ∧ ¬ P \\
  \hline
  T & F & F \\
  F & T & F \\
  \hline
\end{array}
$$
-/
TheoremDoc And_not_self as "EQU: And_not_self"


/--This is an **Identity Law**. It says that

$$ P ∧ T₀ ↔ P $$

where $T₀$ is a tautology. We can prove the **Identity Law** with a truth-table:
$$
\begin{array}{|cc||c|}
  \hline
  P & T₀ & P ∧ T₀ \\
  \hline
  T & T & T \\
  F & T & F \\
  \hline
\end{array}
$$
-/
TheoremDoc And_true as "EQU: And_true"




/--This is a **Domination Law**. It says that

$$ P ∨ T₀ ↔ T₀ $$

where $T₀$ is a tautology. We can prove the **Domination Law** with a truth-table:
$$
\begin{array}{|cc||c|}
  \hline
  P & T₀ & P ∨ T₀ \\
  \hline
  T & T & T \\
  F & T & T \\
  \hline
\end{array}
$$
-/
TheoremDoc Or_true as "EQU: Or_true"

/--This is a **Domination Law**. It says that

$$ P ∧ F₀ ↔ F₀ $$

where $F₀$ is a contradiction. We can prove the **Domination Law** with a truth-table:
$$
\begin{array}{|cc||c|}
  \hline
  P & F₀ & P ∧ F₀ \\
  \hline
  T & F & F \\
  F & F & F \\
  \hline
\end{array}
$$
-/
TheoremDoc And_false as "EQU: And_false"

/--
The negated conjunction of $P$ with itself is logically equivalent to $¬ P$.
-/
TheoremDoc Nand_self as "EQU: Nand_self"

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

We can prove the **Idempotent Law** with a truth-table:
$$
\begin{array}{|c||c|}
  \hline
  P & P ∨ P \\
  \hline
  T & T & T \\
  F & T & F \\
  \hline
\end{array}
$$
-/
TheoremDoc Or_self as "EQU: Or_self"

/--
This is an **Idempotent Law**. It says that

$$ P ∧ P ↔ P $$

We can prove the **Idempotent Law** with a truth-table:
$$
\begin{array}{|c||c|}
  \hline
  P & P ∧ P \\
  \hline
  T & T & T \\
  F & T & F \\
  \hline
\end{array}
$$
-/
TheoremDoc And_self as "EQU: And_self"

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

/--
This theorem says that

$$ (P → (Q ∨ R)) ↔ (P → (¬ Q → R))$$

In other words, if you want to prove and if-then statement where the conclusion is a disjunction, then you may do so by... **assuming** that `P` and `¬ Q` are true (by **currying**), and then showing that `R` must follow.
-/
TheoremDoc Imp_or_iff_imp_not_imp as "EQU: Imp_or_iff_imp_not_imp"
