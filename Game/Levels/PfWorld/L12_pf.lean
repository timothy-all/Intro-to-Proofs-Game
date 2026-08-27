import Game.Levels.PfWorld.L11_pf

World "PfWorld"
Level 12

Title "Custom cases"

Introduction "
# **Level 12: Custom cases**
There are other situations in which we might want to use custom case work. For example, consider the claim:
> *For every integer $n$, $n^2 - n$ is even.
>
A natural way to argue (and think about) this statement is to start by saying:
> *Let $n$ be an integer. Then either $n$ is even, or $n$ is not even...
>
This example gives us some practice with similar reasoning.
>
First, let's reckon with the universal statement in the goal and `intro` a generic variable.
"


/-- Let $A,B,C$ be sets and suppose the following: the symmetric difference $(A \ B) ∪ (B \ A)$ is contained in $C$, $B$ is contained in $C$, and $Bᶜ$ is contained in $A$. Then everything belongs to $C$.-/
Statement {u : Type*} (A B C : Set u) (h : (A \ B ∪ B \ A) ⊆ C) (hB : B ⊆ C) (hB' : Bᶜ ⊆ A): ∀ x, x ∈ C := by
  intro x
  Hint "From here, we might be tempted to argue like the following:
  > *Either `{x} ∈ B` or `¬ {x} ∈ B`.
  >
  Use `by_cases` to split our goal according to this dichotomy."
  by_cases hxb : x ∈ B
  Hint "Great. We can clear this subgoal in one line."
  exact hB hxb
  Hint "Perfect. See if you can't finish this level on your own."
  obtain hxa := hB' hxb
  obtain want : x ∈ A \ B ∪ B \ A
  left
  exact And.intro hxa hxb
  exact h want


Conclusion ""
