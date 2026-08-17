import Game.Levels.SetWorld.Metadata_setworld
import Game.Levels.PfWorld.Metadata_pfworld

theorem double_inclusion {α : Type u} {a b : Set α} (h₁ : a ⊆ b) (h₂ : b ⊆ a) : a = b := by
apply Set.Subset.antisymm
exact h₁
exact h₂

def Rel (u v: Type*) := u → v → Prop

def Rel.set {u v : Type*} (R: Rel u v) := {(a,b) | R a b}

def Rel.inv {u v : Type*} (R: Rel u v) : Rel v u := fun (b : v) (a : u) => R a b

def Rel_subrel {u v : Type*} (R: Rel u v) (S: Rel u v) : Prop := ∀ a b, R a b → S a b

def Rel.dom {u v : Type*} (R: Rel u v) := {a | ∃ b, R a b}

def Rel.range {u v : Type*} (R: Rel u v) := {b | ∃ a, R a b}

def Rel_comp {u v w: Type*} (S: Rel v w) (R: Rel u v) : Rel u w :=
  fun (a: u) (c: w) => ∃ b, (R a b) ∧ (S b c)
infix:70 " ∘ " => Rel_comp

def Rel_on (u : Type*) := Rel u u

def Rel_id (u : Type*) : Rel_on u := fun (u1: u) (u2: u) => u1 = u2

def Rel_union {u v : Type*} (R S : Rel u v) : Rel u v := fun (a : u) (b : v) => R a b ∨ S a b

def isReflexive {u : Type*} (R: Rel_on u) := ∀ a, R a a

def isSymmetric {u : Type*} (R: Rel_on u) := ∀ {a b}, (R a b) → (R b a)

def isAntisymmetric {u : Type*} (R: Rel_on u) := ∀ {a b}, ((R a b) ∧ (R b a)) → a = b

def isTransitive {u : Type*} (R: Rel_on u) := ∀ {a b c}, (R a b) → (R b c) → (R a c)

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

def isInjective {u v : Type*} (R: Rel u v) := ∀ {a b c}, R a c → R b c → a = b

def isSurjective {u v : Type*} (R: Rel u v) := ∀ b, ∃ a, R a b

def isBijection {u v : Type*} (R: Rel u v) := isInjective R ∧ isSurjective R

def Rel_fiberrel {u v: Type*} (g: Rel u v) : Rel_on u := by
  intro x1 x2
  exact ∃ y, g x1 y ∧ g x2 y

theorem Rel_subrel_set {u v : Type*} (R: Rel u v) (S: Rel u v) (h: Rel_subrel R S) : R.set ⊆ S.set := by
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

theorem mem_union.{u} {α : Type u} (x : α) (a b : Set α) : x ∈ a ∪ b ↔ x ∈ a ∨ x ∈ b := by
  rw[Set.mem_union]

theorem mem_inter.{u} {α : Type u} (x : α) (a b : Set α) : x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b := by
  rw [Set.mem_inter_iff]

theorem mem_prod {α : Type u} {β : Type v} (s : Set α) (t : Set β) (p : α × β) : p ∈ s ×ˢ t ↔ p.fst ∈ s ∧ p.snd ∈ t := by
  exact Set.mem_prod

theorem snd_not_mem_not_mem_prod (u v: Type) (A: Set u) (B: Set v) (x : u) (y: v) (h: y ∉ B) : (x,y) ∉ (A ×ˢ B) := by
  rw [mem_prod,not_and_or]
  apply Or.intro_right
  exact h
