import GameServer
import Game.Levels.RelationWorld.Metadata_RelationWorld
--import Mathlib.Tactic.Common
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Operations
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Tactic.Common
-- Hello

open Classical


def isFunction {u v: Type*} (R: Rel u v) := ∀ a, ∃! b, R a b

def image {u v : Type*} (R: Rel u v) (U : Set u) : Set v := { v | ∃ u ∈ U, R u v}

def invimage {u v : Type*} (R: Rel u v) (V : Set v) : Set u := { u | ∃ v ∈ V, R u v}


def isInjective {u v : Type*} (R: Rel u v) := ∀ {a b c}, R a c → R b c → a = b
/- Original Fun_isInjective is below. This definition isn't good because it doesn't assume  R a c and R b c. Without this, it could be possible that R a c and R b c are false, and in applications it could be impossible to conclude a = b from this
def Fun_isInjective {u v : Type*} (R: Rel u v) := ∀ a b c, R a c = R b c → a = b
-/

def isSurjective {u v : Type*} (R: Rel u v) := ∀ b, ∃ a, R a b

def isBijection {u v : Type*} (R: Rel u v) := isInjective R ∧ isSurjective R

def Rel_fiberrel {u v: Type*} (g: Rel u v) : Rel_on u := by
  intro x1 x2
  exact ∃ y, g x1 y ∧ g x2 y




--noncomputable def eval {u v : Type*} (f : Rel u v) {h: isFunction f} (a : u) : v := by
--  obtain hfa := h a
--  sorry




/- Logic -/

def Nand (P Q : Prop) : Prop := ¬ (P ∧ Q)
infix:70 " ⊼ " => Nand

theorem nand_def (P Q : Prop) : P ⊼ Q ↔ ¬ (P ∧ Q) := Iff.rfl

-- xor_def : P ⊻ Q ↔  (P ∧ ¬Q) ∨ (Q ∧ ¬P) weird that Xor is known but not Nand
infix:70 " ⊻ " => Xor'


def Rela (u v: Type) := u → v → Prop

def Rela.set (R: Rela u v) := {(a,b) | R a b}

namespace Rela

scoped notation:50 a:50 " [" R "] " b:50 => R a b

def exrel : Rela ℕ ℕ := fun a b => a = b

example : 2 [exrel] 2 := by
  unfold exrel
  rfl


end Rela

syntax "simplify" : tactic
macro_rules
| `(tactic| simplify) => `(tactic| push_cast; ring)

/-
syntax "use! " term : tactic
macro_rules
  | `(tactic| use! $w) =>
      `(tactic| refine Exists.intro $w ?_; dsimp)


syntax "simplify2" : tactic
macro_rules
  | `(tactic| simplify2) =>
    `(tactic| (try simp only [pow_add, pow_mul, mul_pow, pow_succ, pow_zero, pow_one, one_pow]; ring))
-/
--Divisibility definitions

def Divides (x y : Int) := ∃ z, x * z = y

def isEven (x : Int) := ∃ k, x = 2 * k

def isOdd (x : Int) := ∃ k, x = 2 * k + 1
