import GameServer
import Mathlib.Tactic.Common
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Operations
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
-- import Mathlib.Tactic.Common
-- Hello

open Classical

@[simp]
theorem Imp_iff_not_or (P Q : Prop) : (P → Q) ↔ (¬ P ∨ Q) := by
  rw[imp_iff_not_or]

theorem Contra (P Q : Prop) : (P → Q) ↔ (¬ Q → ¬ P) := by
  repeat rw[Imp_iff_not_or]
  rw[Classical.not_not]
  rw[Or.comm]

theorem Not_and (P Q : Prop) : ¬ (P ∧ Q) ↔ (¬ P ∨ ¬ Q) := by
  simp -- not_and_of_not_or_not

theorem Not_or (P Q : Prop) : ¬ (P ∨ Q) ↔ (¬ P ∧ ¬ Q) := by
  simp

theorem Or_comm (P Q : Prop) : P ∨ Q ↔ Q ∨ P := by
  exact Or.comm

theorem And_comm (P Q : Prop) : P ∧ Q ↔ Q ∧ P := by
  exact And.comm

theorem And_assoc (P Q R : Prop) : ((P ∧ Q) ∧ R) ↔ (P ∧ (Q ∧ R)) := by
  exact and_assoc

theorem Or_assoc (P Q R : Prop) : ((P ∨ Q) ∨ R) ↔ (P ∨ (Q ∨ R)) := by
  exact or_assoc

theorem And_or_left (P Q R : Prop) : (P ∧ (Q ∨ R)) ↔ ((P ∧ Q) ∨ (P ∧ R)) := by
  exact and_or_left

theorem Or_and_left (P Q R : Prop) : (P ∨ (Q ∧ R)) ↔ ((P ∨ Q) ∧ (P ∨ R)) := by
  exact or_and_left

theorem Not_not (P : Prop) : ¬ ¬ P ↔ P := by
  exact Classical.not_not

theorem And_self (P : Prop) : (P ∧ P) ↔ P := by
  simp

theorem Or_self (P : Prop) : (P ∨ P) ↔ P := by
  simp

theorem And_true (P : Prop) : P ∧ True ↔ P := by
  simp

theorem True_and (P : Prop) : True ∧ P ↔ P := by
  simp

theorem Or_true (P : Prop) : P ∨ True ↔ True := by
  simp

theorem True_or (P : Prop) : True ∨ P ↔ True := by
  simp

theorem And_false (P : Prop) : P ∧ False ↔ False := by
  simp

theorem False_and (P : Prop) : False ∧ P ↔ False := by
  simp

theorem Or_false (P : Prop) : P ∨ False ↔ P := by
  simp

theorem False_or (P : Prop) : False ∨ P ↔ P := by
  simp

theorem Or_not_self (P : Prop) : P ∨ ¬ P ↔ True := by
  simp
  by_cases h : P
  repeat simp[h]

theorem Not_self_or (P : Prop) : ¬ P ∨ P ↔ True := by
  rw[or_comm]
  rw[Or_not_self]

theorem And_not_self (P : Prop) : P ∧ ¬ P ↔ False := by
  simp

/- Set structure -/

theorem mem_union.{u} {α : Type u} (x : α) (a b : Set α) : x ∈ a ∪ b ↔ x ∈ a ∨ x ∈ b := by
  rw[Set.mem_union]

theorem mem_inter.{u} {α : Type u} (x : α) (a b : Set α) : x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b := by
  rw [Set.mem_inter_iff]

theorem mem_prod {α : Type u} {β : Type v} (s : Set α) (t : Set β) (p : α × β) : p ∈ s ×ˢ t ↔ p.fst ∈ s ∧ p.snd ∈ t := by
  exact Set.mem_prod

theorem mem_univ_iff_true {u : Type} (a : u) : a ∈ Set.univ ↔ True := by
  simp

/-
Indexed families are a little tricky. An indexed family is a function from I (some Sort) to u (some Type -- btw, Type u is shorthand for Sort (u+1)). So what we might write as {Aᵢ : i ∈ I} in class is handled as A : I → Set u in Lean. Unraveling things further, Lean considers
⋂ i, A i = sInf (Set.range A)
which itself expands to
⋂ i, A i = sInf { B : Set u | ∃ (i : I), A i = B}
At this point things get handled the same way as families of sets.

-/

theorem mem_iunion {u : Type*} {x : u} {I : Type*} (A : I → Set u) : x ∈ ⋃ i, A i ↔ ∃ (i : I), x ∈ A i := by
  simp

theorem mem_iinter {u : Type*} {x : u} {I : Type*} (A : I → Set u) : x ∈ ⋂ i, A i ↔ ∀ (i : I), x ∈ A i := by
  simp

theorem mem_finter {u : Type*} {x : u} (F : Set (Set u)) : x ∈ ⋂₀ F ↔ ∀ (t : Set u), t ∈ F → x ∈ t := by
  simp

theorem mem_funion {u : Type*} {x : u} (F : Set (Set u)) : x ∈ ⋃₀ F ↔ ∃ t ∈ F, x ∈ t := by
  simp

-- Theorem below should be unlocked following level 2 of Cartesian products since we prove the fst version
theorem snd_not_mem_not_mem_prod (u v: Type) (A: Set u) (B: Set v) (x : u) (y: v) (h: y ∉ B) : (x,y) ∉ (A ×ˢ B) := by
  rw [mem_prod,Not_and]
  apply Or.intro_right
  exact h


theorem double_inclusion {α : Type u} {a b : Set α} (h₁ : a ⊆ b) (h₂ : b ⊆ a) : a = b := by
apply Set.Subset.antisymm
exact h₁
exact h₂


/- Theorem below isn't needed; using `intro x` will just unpack a subset statement directly -/
theorem subset_def {α : Type u} (s t : Set α) : (s ⊆ t) = ∀ x ∈ s, x ∈ t := by
  exact Set.subset_def




/- Relations -/

def Rel (u v: Type*) := u → v → Prop

def Rel.set (R: Rel u v) := {(a,b) | R a b}

--infix test below
namespace Rel

scoped notation:50 a:50 " ~[" R "] " b:50 => (a, b) ∈ Rel.set R

def exrel : Rel ℕ ℕ := fun (a: ℕ) (b: ℕ) => (a=b)

#check (2,2) ∈ exrel.set
#check 2 ~[exrel] 2

end Rel

def Rel.inv {u v : Type*} (R: Rel u v) : Rel v u := fun (b : v) (a : u) => R a b

def Rel_subrel (R: Rel u v) (S: Rel u v) : Prop := ∀ a b, R a b → S a b

def Rel.dom {u v : Type*} (R: Rel u v) := {a | ∃ b, R a b}

def Rel.range {u v : Type*} (R: Rel u v) := {b | ∃ a, R a b}

def Rel_comp {u v w: Type*} (S: Rel v w) (R: Rel u v) : Rel u w :=
  fun (a: u) (c: w) => ∃ b, (R a b) ∧ (S b c)
infix:70 " ∘ " => Rel_comp

def Rel_on (u : Type*) := Rel u u

def Rel_id (u : Type*) : Rel_on u := fun (u1: u) (u2: u) => u1 = u2

def Rel_union {u v : Type*} (R S : Rel u v) : Rel u v := fun (a : u) (b : v) => R a b ∨ S a b

/- This is a level in relation world -/
--theorem Rel_id_set {u : Type} : (Rel_id u).set = {(a,a) | a : u} := by


def isReflexive {u : Type*} (R: Rel_on u) := ∀ a, R a a

def isSymmetric {u : Type*} (R: Rel_on u) := ∀ a b, (R a b) → (R b a)

def isAntisymmetric {u : Type*} (R: Rel_on u) := ∀ a b, ((R a b) ∧ (R b a)) → a = b

def isTransitive {u : Type*} (R: Rel_on u) := ∀ a b c, (R a b) → (R b c) → (R a c)

structure isPartialOrder {u : Type*} (R : Rel_on u) where
  (refl : isReflexive R)
  (anti : isAntisymmetric R)
  (tran : isTransitive R)

structure isEquivalence {u : Type*} (R : Rel_on u) where
  (refl : isReflexive R)
  (symm : isSymmetric R)
  (tran : isTransitive R)




def isMinimal {u : Type*} (R: Rel_on u) (b : u) (B : Set u := Set.univ) := b ∈ B ∧ ∀ x, x ∈ B → R x b → x = b

def isMaximal {u : Type*} (R: Rel_on u) (b : u) (B : Set u := Set.univ) := b ∈ B ∧ ∀ x, x ∈ B → R b x → x = b

def isSmallest {u : Type*} (R: Rel_on u) (b : u) (B : Set u := Set.univ) := b ∈ B ∧ ∀ x, x ∈ B → R b x

def isLargest {u : Type*} (R: Rel_on u) (b : u) (B : Set u := Set.univ) := b ∈ B ∧ ∀ x, x ∈ B → R x b

def isLowerBound {u : Type*} (R: Rel_on u) (l : u) (B : Set u := Set.univ) := ∀ x, x ∈ B → R l x

def isUpperBound {u : Type*} (R: Rel_on u) (s : u) (B : Set u := Set.univ) := ∀ x, x ∈ B → R x s

def LowerBounds {u : Type*} (R : Rel_on u) (B : Set u := Set.univ) := {l | isLowerBound R l B}

def UpperBounds {u : Type*} (R : Rel_on u) (B : Set u := Set.univ) := {l | isUpperBound R l B}

def isInfimum {u : Type*} (R: Rel_on u) (l : u) (B : Set u := Set.univ) := isLargest R l (LowerBounds R B)

def isSupremum {u : Type*} (R: Rel_on u) (s : u) (B : Set u := Set.univ) := isSmallest R s (UpperBounds R B)

def subsetOrderOrig {u : Type*} (S: Set u) : Rel_on {V // V ⊆ S} := fun (A : {V // V ⊆ S}) (B : {V // V ⊆ S}) => A.val ⊆ B.val
def subsetOrder (u : Type*) : Rel_on (Set u) := fun (A : Set u) (B : Set u) => A ⊆ B


def equivClass {u : Type*} (R: Rel_on u) (a : u) := {x | R a x}

def equivClassFamily {u : Type*} (R: Rel_on u) := {equivClass R x | x : u}

def isFunction {u v: Type*} (R: Rel u v) := ∀ a, ∃! b, R a b

def image {u v : Type*} (R: Rel u v) (U : Set u) : Set v := { v | ∃ u ∈ U, R u v}

def invimage {u v : Type*} (R: Rel u v) (V : Set v) : Set u := { u | ∃ v ∈ V, R u v}


def isInjective {u v : Type*} (R: Rel u v) := ∀ a b c, R a c → R b c → a = b
/- Original Fun_isInjective is below. This definition isn't good because it doesn't assume  R a c and R b c. Without this, it could be possible that R a c and R b c are false, and in applications it could be impossible to conclude a = b from this
def Fun_isInjective {u v : Type*} (R: Rel u v) := ∀ a b c, R a c = R b c → a = b
-/

def isSurjective {u v : Type*} (R: Rel u v) := ∀ b, ∃ a, R a b

def isBijection {u v : Type*} (R: Rel u v) := isInjective R ∧ isSurjective R

def Rel_fiberrel {u v: Type*} (g: Rel u v) : Rel_on u := by
  intro x1 x2
  exact ∃ y, g x1 y ∧ g x2 y

open Lean Elab Tactic

syntax "evaluate " term " at " term " with " ident ident ident : tactic
elab_rules : tactic
| `(tactic| evaluate $f at $a with $b $hbf $hbu) => do
      evalTactic (← `(tactic|
        obtain ⟨$b,⟨__a,__b⟩⟩ := $f $a; dsimp at __b; rename_i $hbu:ident; rename_i $hbf:ident;
      ))



noncomputable def eval {u v : Type*} (f : Rel u v) {h: isFunction f} (a : u) : v := by
  obtain hfa := h a
  sorry



theorem Rel_subrel_set (R: Rel u v) (S: Rel u v) (h: Rel_subrel R S) : R.set ⊆ S.set := by
  intro x
  intro h1
  apply h at h1
  exact h1

theorem Rel_double_inclusion {u v: Type*} (R: Rel u v) (S: Rel u v) : R.set = S.set → R = S := by
  intro h
  funext x y
  simp
  constructor
  intro h1
  obtain h2 : (x,y) ∈ R.set := by exact h1
  rw [h] at h2
  exact h2
  intro h1
  obtain h2 : (x,y) ∈ S.set := h1
  rw [← h] at h1
  exact h1

/-
def Rel'' {u: Type} {v: Type} (A: Set u) (B: Set v) := A → B → Prop

def Rel.inv {u v : Type} {A : Set u} {B : Set v} (R: Rel A B) : Rel B A :=
  fun (b : B) (a : A) => R a b

/- Set of ordered pairs in a relation -/
def Rel.set {u v : Type} {A : Set u} {B : Set v} (R : Rel A B) :
  Set (u × v) :=
{ p | ∃ (a : A) (b : B), p = ((a : u), (b : v)) ∧ R a b }

def Rel.dom {u v : Type} {A : Set u} {B: Set v} (R: Rel A B) := {a | ∃ b, (a,b) ∈ R.set}

def Rel.range {u v : Type} {A : Set u} {B: Set v} (R: Rel A B) := {b | ∃ a, (a,b) ∈ R.set}

def Rel.comp {u v w: Type} {A: Set u} {B: Set v} {C: Set w} (S: Rel B C) (R: Rel A B) : Rel A C :=
 fun (a : A) (c : C) => ∃ b : B, R a b ∧ S b c

notation:50 S " ∘ " R => Rel.comp S R


/- Possible alternative relation structure -/
structure Rel' {u v: Type} (A: Set u) (B: Set v) where
  pairs : Set (u × v)
  subset : pairs ⊆ A ×ˢ B

/- User would use Rel_inv' -/
theorem Rel_swap' {u v: Type} {A: Set u} {B: Set v} (R: Rel' A B) : {(b,a) | (a,b) ∈ R.pairs} ⊆ B ×ˢ A := by
  intro x
  intro s
  simp at s
  apply R.subset at s
  rw [mem_prod] at s
  rw [mem_prod, and_comm]
  exact s

def Rel_inv' {u v : Type} {A: Set u} {B: Set v} (R: Rel' A B) : Rel' B A := { pairs := {(b,a) | (a,b) ∈ R.pairs}, subset := Rel_swap' R}

def Rel_dom' {u v : Type} {A : Set u} {B: Set v} (R: Rel' A B) : Set u := { a | ∃ b, (a,b) ∈ R.pairs}

def Rel_range' {u v : Type} {A : Set u} {B: Set v} (R: Rel' A B) : Set u := { b | ∃ a, (b,a) ∈ R.pairs}

/- Used to build a composite relation -/
theorem Rel_comp_proof' {u v w: Type} {A: Set u} {B: Set v} {C: Set w} (S: Rel' B C) (R: Rel' A B) : {(a,c) | ∃ b, (a,b) ∈ R.pairs ∧ (b,c) ∈ S.pairs} ⊆ A ×ˢ C := by
  intro x
  intro s
  simp at s
  rcases s with ⟨y, ⟨hy1,hy2⟩⟩
  apply R.subset at hy1
  apply S.subset at hy2
  rw [mem_prod] at hy1
  rw [mem_prod] at hy2
  rw [mem_prod]
  constructor
  exact hy1.left
  exact hy2.right

def Rel_comp' {u v w: Type} {A: Set u} {B: Set v} {C: Set w} (S: Rel' B C) (R: Rel' A B) : Rel' A C := {pairs := {(a,c) | ∃ b, (a,b) ∈ R.pairs ∧ (b,c) ∈ S.pairs}, subset := Rel_comp_proof' S R}
-/

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
| `(tactic| simplify) => `(tactic| ring)

syntax "use! " term : tactic
macro_rules
  | `(tactic| use! $w) =>
      `(tactic| refine Exists.intro $w ?_; dsimp)

--Divisibility definitions

def Divides (x y : Int) := ∃ z, x * z = y

def isEven (x : Int) := ∃ k, x = 2 * k

def isOdd (x : Int) := ∃ k, x = 2 * k + 1
