import GameServer


/--
This is a finishing tactic. Typical usage might look like
```
exact s
```
where `s` is known (provable) statement. Lean will clear the goal if `s` matches the target.
-/
TacticDoc exact

/--
The `obtain` tactic is used bring new (and provable) hypotheses into the proof state. It can also be used to desctructure existing assumptions.
-/
TacticDoc obtain

/--
The `intro` tactic introduces hypotheses (from the goal) into the proof state. Typical usage might look like the following. If the goal is:
```
⊢ P → Q
```
Then `intro hP` will introduce the hypothesis `hP : P` into the proof state.

### **Universal generalization**
The `intro` tactic is also good for introducing generic variables associated to a universally quantified goal. For example, if our goal is of the form:
```
⊢ ∀ x, P x
```
Then
```
intro a
```
will make `a : u` an object and our goal becomes `⊢ P a`.
-/
TacticDoc intro


/--
This is the constructor for the `∧` logical connective. As a (curried) function, it looks like the following:
```
And.intro : P → Q → P ∧ Q
```
Typical usage might look like the following. Suppose we have the hypotheses:
```
hP : P
hQ : Q
```
Then
```
obtain hPQ := And.intro hP hQ
```
will introduce the new hypothesis `hPQ : P ∧ Q` into the proof-state.
-/
DefinitionDoc And.intro as "And.intro"
