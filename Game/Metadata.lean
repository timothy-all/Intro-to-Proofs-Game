import GameServer
import Mathlib.Tactic.Common
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Operations
import Mathlib.Data.Set.Lattice
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

-- Theorem below should be unlocked following level 2 of Cartesian products since we prove the fst version
theorem snd_not_mem_not_mem_prod (u v: Type) (A: Set u) (B: Set v) (x : u) (y: v) (h: y ∉ B) : (x,y) ∉ (A ×ˢ B) := by
  rw [mem_prod,Not_and]
  apply Or.intro_right
  exact h

theorem mem_diff.{u} {α : Type u} {s t : Set α} (x : α) : x ∈ s \ t ↔ x ∈ s ∧ x ∉ t := by
  rw[Set.mem_diff]


theorem double_inclusion {α : Type u} {a b : Set α} (h₁ : a ⊆ b) (h₂ : b ⊆ a) : a = b := by
apply Set.Subset.antisymm
exact h₁
exact h₂

theorem subset_def {α : Type u} (s t : Set α) : (s ⊆ t) = ∀ x ∈ s, x ∈ t := by
  exact Set.subset_def

/- Relations -/


/- Defines `R a b` for a relates to b under R -/
def Rel {u v: Type} (A: Set u) (B: Set v) := A → B → Prop

def Rel_inv {u v : Type} {A : Set u} {B : Set v} (R: Rel A B) := B → A → (Rel A B)

/- Set of ordered pairs in a relation -/
def Rel_set {u v : Type} (A: Set u) (B: Set v) (R: Rel A B) := {(a,b) | R a b}

def Rel_dom {u v : Type} {A : Set u} {B: Set v} (R: Rel A B) := {a | ∃ b : B, R a b}

def Rel_range {u v : Type} {A : Set u} {B: Set v} (R: Rel A B) := {b | ∃ a : A, R a b}

def Rel_comp {u v w: Type} {A: Set u} {B: Set v} {C: Set w} (S: Rel B C) (R: Rel A B) := {(a,c) | ∃ b : B, (R a b) ∧ (S b c)}
infix:70 " ∘ " => Rel_comp

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
/- Logic -/

def Nand (P Q : Prop) : Prop := ¬ (P ∧ Q)
infix:70 " ⊼ " => Nand

theorem nand_def (P Q : Prop) : P ⊼ Q ↔ ¬ (P ∧ Q) := Iff.rfl

-- xor_def : P ⊻ Q ↔  (P ∧ ¬Q) ∨ (Q ∧ ¬P) weird that Xor is known but not Nand
infix:70 " ⊻ " => Xor'
