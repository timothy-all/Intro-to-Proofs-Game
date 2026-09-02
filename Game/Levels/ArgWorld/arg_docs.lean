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
The `obtain` tactic is used bring new (and provable) assumptions into the proof state. It can also be used to desctructure existing assumptions.
### Basic Usage ###
The most basic usage of the `obtain` tactic might look like the following:
```
obtain ⟨id⟩ := ⟨proof⟩
```
where `⟨id⟩` is the name you want to give (or *identifier*) for the proposition you wish to bring into the proof-state, and `⟨proof⟩` is a (short) proof of that proposition. In some cases, you may wish to explicitly provide the form of the proposition being brought in:
```
obtain ⟨id⟩ : ⟨prop⟩ := ⟨proof⟩
```
where `⟨prop⟩` is the form of the proposition. This is helpful if `⟨prop⟩` is definitionally equivalent to the proposition whose `⟨proof⟩` is provided.

### Opening a New Goal###
If the proof of the proposition you wish to bring into the proof-state requires the use of tactics, you can use the `obtain` tactic to open a new goal in which those tactics can be applied. For example:
```
obtain ⟨id⟩ : ⟨prop⟩
```
will create a new goal whose target is `⊢ ⟨prop⟩`.

### Advanced Usage ###
The `obtain` tactic can simultaneously destructure those propositions brought into the proof-state as assumptions. Typical usage looks like:
```
obtain ⟨patt⟩ := ⟨proof⟩
```
where `⟨patt⟩` is a pattern as in the tactic `rcases`.
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
DefinitionDoc And.intro as "ARG: And.intro"

/--
The `left` tactic is useful for targeting goals that are disjunctions. Specifically, if our goal is of the form `⊢ P ∨ Q`, the tactic `left` will make our new goal `⊢ P`.
-/
TacticDoc left

/--
The `right` tactic is useful for targeting goals that are disjunctions. Specifically, if our goal is of the form `⊢ P ∨ Q`, the tactic `right` will make our new goal `⊢ Q`.
-/
TacticDoc right
