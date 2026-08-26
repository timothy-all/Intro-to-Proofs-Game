import Game.Levels.RelationWorld.Metadata_RelationWorld

open Lean Elab Tactic

syntax "evaluate " term " at " term " with " ident ident ident : tactic
elab_rules : tactic
| `(tactic| evaluate $f at $a with $b $hbf $hbu) => do
      evalTactic (← `(tactic|
        obtain ⟨$b,⟨__a,__b⟩⟩ := $f $a; dsimp at __b; rename_i $hbu:ident; rename_i $hbf:ident;
      ))

def image {u v : Type*} (R: Rel u v) (U : Set u) : Set v := { v | ∃ u ∈ U, R u v}

def invimage {u v : Type*} (R: Rel u v) (V : Set v) : Set u := { u | ∃ v ∈ V, R u v}

def isInjective {u v : Type*} (R: Rel u v) := ∀ {a b c}, R a c → R b c → a = b

def isSurjective {u v : Type*} (R: Rel u v) := ∀ b, ∃ a, R a b

def isBijection {u v : Type*} (R: Rel u v) := isInjective R ∧ isSurjective R

def Rel_fiberrel {u v: Type*} (R: Rel u v) : Rel_on u := fun x1 x2 => ∃ y, R x1 y ∧ R x2 y
