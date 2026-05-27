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
-/
TheoremDoc Imp_iff_not_or as "Imp_iff_not_or"

/--
This is the **Commutative Law** for `∨`. It says that

$$ (P ∨ Q) ↔ (Q ∨ P) $$

Here's what it looks like in Lean:
```
Or_comm (P Q : Prop) : P ∨ Q ↔ Q ∨ P
```
-/
TheoremDoc Or_comm as "Or_comm"

/--
This is the **Double Negation Law**. It says that

$$ ¬ ¬ P ↔ P $$
-/
TheoremDoc Not_not as "Not_not"

/--
An implication is logically equivalent to its contrapositive.
-/
TheoremDoc Contrapositive as "Contrapositive"

/--
The tactic `rw` is the same as `rewrite` except it automatically attempts to clear the goal with `rfl` at the end. This can often save us a line.
-/
TacticDoc rw

/--
This is the **Associative Law** for `∨`. It says that

$$ (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R) $$
-/
TheoremDoc Or_assoc as "Or_assoc"

/-- This is half of **DeMorgan's Law**. It says that

$$ ¬ (P ∧ Q) ↔ (¬ P ∨ ¬ Q)$$

Here's what it looks like in Lean:
```
Not_and (P Q : Prop) : ¬ (P ∧ Q) ↔ (¬ P ∨ ¬ Q)
```
 -/
TheoremDoc Not_and as "Not_and"

/--
This is known as **currying**. It says that

$$ (P ∧ Q) → R ↔ P → (Q → R) $$
-/
TheoremDoc Curry as "Curry"

/--
This is the **Associative Law** for `∧`. It says that

$$ (P ∧ Q) ∧ R ↔ P ∧ (Q ∧ R) $$
-/
TheoremDoc And_assoc as "And_assoc"

/--
This is the **Commutative Law** for `∧`. It says that

$$ P ∧ Q ↔ Q ∧ P $$
-/
TheoremDoc And_comm as "And_comm"
