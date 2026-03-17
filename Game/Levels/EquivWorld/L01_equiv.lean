import Game.Metadata

World "EquivWorld"
Level 1

Title "Test"

Introduction "
### **🤔 Level 1?**
We've unlocked two theorems for this first level, namely: `or_comm` and `not_or_imp`. 🔍 Check out the entries for these theorems in the **Theorems** tab.
"

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

$$ (¬ P ∨ Q) ↔ (P → Q) $$
-/
TheoremDoc Or_imp as "Or_imp"

/--
This is the **Commutative Law** for `∨`. It says that

$$ (P ∨ Q) ↔ (Q ∨ P) $$
-/
TheoremDoc Or_comm as "Or_comm"


Statement (P Q : Prop) : (P → Q) ↔ Q ∨ ¬ P := by
  Hint "The conditional law says that `P → Q` is logically equivalent to `¬ P ∨ Q`. This looks *very* close to that statement. We might start by ***rewriting*** the right-hand side of our goal...
  ### ❯ The `rewrite` tactic
  In order to apply ***rewrites*** (or substitutions) in Lean, we use the `rewrite` tactic. 🔍 Check out the entry for `rewrite` in the **Tactics** tab for details. 👉 In this specific case, try
  ```
  rewrite[Or_comm]
  ```
  This will apply the **Commutative Law** for `∨` at the first instance in the goal where it is applicable (namely, the right-hand side in this case). 🔍 Check out the entry for `Or_comm` in the **Theorems** tab.
  "
  rewrite[Or_comm]
  Hint "We should now rewrite the left-hand side of our goal using the **Conditional Law**..."
  rewrite[Or_imp]
  Hint "
  ### ❯ The `rfl` tactic
  Our goal is currently `(P → Q) ↔ (P → Q)` ... this is true by reflexitivity! The tactic that clears the goal is `rfl`. 🔍 Check out the entry for `rfl` in the **Tactics** tab. 👉 In our case, try:
  ```
  rfl
  ```
  "
  rfl

Conclusion "
### ***🥳 Congrats!***
You beat the first level! We'll add more **Theorems** (known logical equivalences) as we progress through the world.
"

NewTactic rewrite rfl
NewTheorem Or_imp Or_comm
