import GameServer

/--
The tactic `rewrite[e]` applies the identity/equivalence `e` as a **rewrite** rule to the target.

If `e` is preceded by left arrow (`←` or `<-`), the rewrite is applied in the reverse direction. For example, if `e : a = b` then ...
* `rewrite[e]` replaces all instances of `a` with `b` in the target
* `rewrite[← e]` replaces all instances of `b` with `a` in the target

If `e₁`,`e₂`,...,`eₙ` is a sequence of identities then
```
rewrite [e₁, ..., eₙ]
```
applies the given rules sequentially.

Finally, `rewrite [e] at l` rewrites `e` at location(s) `l`, where `l` is a list of hypotheses in the local context or the main goal `⊢` (or `|-`).

### **⌨ Typesetting tip**
To pretty print the left-arrow `←` use `\\left`. To pretty print the symbol `⊢` use `\\vdash`.
-/
TacticDoc rewrite

/--
This tactic clears a goal whose target has the form `x = x` or `P ↔ P` (or `x ~ x` where `∼` is any relation that has a reflexivity lemma tagged with the attribute @[refl] -- we'll talk more about relations later).
-/
TacticDoc rfl

/--
This theorem is the so-called **Conditional Law**. It says that

$$ (P → Q) ↔ (¬ P ∨ Q) $$
The proof of `Imp_iff_not_or` follows from the truth-table below:
$$
\begin{array}{|cc||cc|}
  \hline
  P & Q & P → Q & ¬ P ∨ Q  \\
  \hline
  T & T & T & T \\
  T & F & F & F \\
  F & T & T & T \\
  F & F & T & T \\
  \hline
\end{array}
$$
-/

TheoremDoc Imp_iff_not_or as "EQU : Imp_iff_not_or"

/--
This is the **Commutative Law** for `∨`. It says that

$$ (P ∨ Q) ↔ (Q ∨ P) $$

Here's what it looks like in Lean:
```
Or_comm {P Q : Prop} : P ∨ Q ↔ Q ∨ P
```
The proof of `Or_comm` follows from the truth-table below:
$$
\begin{array}{|cc||cc|}
  \hline
  P & Q & P ∨ Q & Q ∨ P  \\
  \hline
  T & T & T & T \\
  T & F & T & T \\
  F & T & T & T \\
  F & F & F & F \\
  \hline
\end{array}
$$
-/
TheoremDoc Or_comm as "EQU : Or_comm"

/--
This is the **Double Negation Law**. It says that

$$ ¬ ¬ P ↔ P $$
Here's what it looks like in Lean:
```
Not_not (P : Prop) : ¬¬ P ↔ P
```
-/
TheoremDoc Not_not as "EQU : Not_not"

/--
An implication is logically equivalent to its contrapositive. We can prove this via a truth-table:
$$
\begin{array}{|cc||c||cc||c|}
  \hline
  P & Q & P → Q & ¬ Q & ¬ P & ¬ Q → ¬ P  \\
  \hline
  T & T & T & F & F & T \\
  T & F & F & T & F & F \\
  F & T & T & F & T & T \\
  F & F & T & T & T & T \\
  \hline
\end{array}
$$
-/
TheoremDoc Contrapositive as "EQU : Contrapositive"

/--
The tactic `rw` is the same as `rewrite` except it automatically attempts to clear the goal with `rfl` at the end. This can often save us a line.
-/
TacticDoc rw

/--
This is the **Associative Law** for `∨`. It says that

$$ (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R) $$
-/
TheoremDoc Or_assoc as "EQU : Or_assoc"

/-- This is half of **DeMorgan's Law**. It says that

$$ ¬ (P ∧ Q) ↔ (¬ P ∨ ¬ Q)$$

Here's what it looks like in Lean:
```
Not_and {P Q : Prop} :
  ¬ (P ∧ Q) ↔ (¬ P ∨ ¬ Q)
```
We can prove DeMorgan's Law with a truth-table:
$$
\begin{array}{|cc||c||cc||c|}
  \hline
  P & Q & ¬ (P ∧ Q) & ¬ P & ¬ Q & ¬ P ∨ ¬ Q  \\
  \hline
  T & T & F & F & F & F \\
  T & F & T & F & T & T \\
  F & T & T & T & F & T \\
  F & F & T & T & T & T \\
  \hline
\end{array}
$$
 -/
TheoremDoc Not_and as "EQU : Not_and"

/--
This is known as **currying**. It says that

$$ (P ∧ Q) → R ↔ P → (Q → R) $$
-/
TheoremDoc Curry as "EQU : Curry"

/--
This is the **Associative Law** for `∧`. It says that

$$ (P ∧ Q) ∧ R ↔ P ∧ (Q ∧ R) $$
Here's what it looks like in Lean:
```
And_assoc (P Q R : Prop) :
  ((P ∧ Q) ∧ R) ↔ (P ∧ (Q ∧ R))
```
The proof of `And_assoc` is given in the truth-table below:
$$
\begin{array}{|ccc||cc|}
  \hline
  P & Q & R & (P ∧ Q) ∧ R & P ∧ (Q ∧ R) \\
  \hline
  T & T & T & T & T \\
  T & T & F & F & F \\
  T & F & T & F & F \\
  T & F & F & F & F \\
  F & T & T & F & F \\
  F & T & F & F & F \\
  F & F & T & F & F \\
  F & F & F & F & F \\
  \hline
\end{array}
$$
-/
TheoremDoc And_assoc as "EQU : And_assoc"

/--
This is the **Commutative Law** for `∧`. It says that

$$ P ∧ Q ↔ Q ∧ P $$
-/
TheoremDoc And_comm as "EQU : And_comm"
