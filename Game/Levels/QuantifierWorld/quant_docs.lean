import GameServer

/--
The `exist` tactic is useful for existential goals. Specifically, if the goal is of the form `⊢ ∃ x, p x`, then assuming `y` is a known object in the tactic state we get that
```
exist y
```
Will change the goal to `⊢ p y`.
-/
TacticDoc exist


/--
The tactic `push_neg` rewrites the goal by pushing negations deeper into an expression. For instance, the goal `¬ ∀ x, ∃ y, x ≤ y` will be transformed by `push_neg` into `∃ x, ∀ y, y < x`.
-/
TacticDoc push_neg


/--
The negation of a univeral statement is an existential statement. Here's a proof in the case that the universe contains two elements:

$$
\begin{aligned}
  ¬ ∀ x ∈ \{ a,b \}, P x & ↔ ¬ (P a ∧ P b) \\
  & ↔ (¬ P a) ∨ (¬ P b) \\
  & ↔ ∃ x ∈ \{a,b\}, ¬ P x
\end{aligned}
$$
-/
TheoremDoc Not_forall as "QUA: Not_forall"

/--
The negation of a univeral statement is an existential statement. Here's a proof in the case that the universe contains two elements:

$$
\begin{aligned}
  ¬ ∃ x ∈ \{ a,b \}, P x & ↔ ¬ (P a ∨ P b) \\
  & ↔ (¬ P a) ∧ (¬ P b) \\
  & ↔ ∀ x ∈ \{a,b\}, ¬ P x
\end{aligned}
$$
-/
TheoremDoc Not_exists as "QUA: Not_exists"

/--
Forall distributes over ands
-/
TheoremDoc Forall_and as "QUA: Forall_and"
