import Game.Levels.InductionWorld.induction_test
import Game.Levels.LeanFunctionWorld.lf_test
import Game.Levels.FunctionWorld.FunctionWorldExamples --I had to import this directly, why wasn't it pulled from inductionworld?

/-Lines below set up sigma notation-/
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.Linarith

open Finset
open BigOperators


World "CardinalityWorld"
Level 1

Title "Cardinality test"

Introduction "."

--Placeholder level
Statement (n : Nat) : true := by
  rfl

Conclusion " "

/-
Main cardinality world goals:
- Equinumerous is an equivalence relation
- ℝ and ℕ are not equinumerous
- ℚ is countable (difficult?)

**HTPIL makes this way easier using usual functions. Maybe it could be worth it to abandon relation-functions here, or maybe start by showing how they fit in with Lean functions?
-/

--Basic cardinality setup and examples



def Equinumerous (u v : Type*) := ∃ f : Rel u v,  isFunction f ∧ isBijection f
infix:70 " ~ " => Equinumerous


--Equinumerous is an equivalence relation

theorem Equinumerous.refl (u : Type*) : u ~ u := by
  use Rel_id u
  refine ⟨Fun_identity_fun, Fun_identity_bij⟩

theorem Equinumerous.symm (u v : Type*) : u ~ v → v ~ u := by
  intro h
  obtain ⟨f,⟨hff,hfb⟩⟩ := h
  use f.inv
  refine ⟨Fun_bij_is_invertible f hff hfb, Fun_invertible_is_bij f.inv (Fun_bij_is_invertible f hff hfb) hff⟩
  --FunctionWorld proves that f invertible → f bij, but not f invertible → f.inv bij. But, with the simple relation definition of function, f.inv.inv is definitionally equivalent to f, so hff is the same as isFunction f.inv.inv

theorem Equinumerous.tran (u v w : Type*) : u ~ v → v ~ w → u ~ w := by
  intro huv hvw
  obtain ⟨fuv, ⟨hfuvf,⟨hfuvi,hfuvs⟩⟩⟩ := huv
  obtain ⟨fvw, ⟨hfvwf,⟨hfvwi,hfvws⟩⟩⟩ := hvw
  use fvw ∘ fuv
  refine ⟨Fun_comp_fun fuv fvw hfuvf hfvwf,?_⟩
  refine ⟨Fun_comp_inj fuv hfuvf hfuvi fvw hfvwf hfvwi,Fun_comp_surj fuv hfuvf hfuvs fvw hfvwf hfvws⟩ --The lemmas Fun_comp_inj and Fun_comp_surj are in functionworldexamples currently


--Equinumerous-related theorems


theorem Card_cartprod_equinumerous {a b c d : Type*} (hab : a ~ b) (hcd : c ~ d) : (a × c) ~ (b × d) := by
  obtain ⟨fab,⟨fabf,⟨fabinj,fabsurj⟩⟩⟩ := hab
  obtain ⟨fcd,⟨fcdf,⟨fcdinj,fcdsurj⟩⟩⟩ := hcd
  use fun x y  => fab x.1 y.1 ∧ fcd x.2 y.2 --Is there a nice name to give this function a name? the proof state looks pretty nasty for most of the proof without a name
  constructor
  intro x
  evaluate fabf at x.1 with y1 fabx1y1Rel fabx1y1Uni
  evaluate fcdf at x.2 with y2 fcdx2y2Rel fcdx2y2Uni
  use! (y1,y2)
  refine ⟨⟨fabx1y1Rel,fcdx2y2Rel⟩,?_⟩
  intro z ⟨fabx1z1,fcdx2z2⟩
  apply fabx1y1Uni z.1 at fabx1z1
  apply fcdx2y2Uni z.2  at fcdx2z2
  rw[← fabx1z1,← fcdx2z2] --end function proof

  constructor
  intro x y z ⟨fabx1z1,fcdx2z2⟩ ⟨faby1z1,fcdy2z2⟩
  rw [Prod.mk_inj] --This is going to have to be either in relationworld or introduced in cardinalityworld
  refine ⟨fabinj fabx1z1 faby1z1, fcdinj fcdx2z2 fcdy2z2⟩ --end injective

  intro z
  obtain ⟨x1,fabx1z1⟩ := fabsurj z.1
  obtain ⟨x2,fcdx2z2⟩ := fcdsurj z.2
  use (x1,x2) --end surjective

--Book has a theorem about taking unions of disjoint sets preserving equinumerous. This is doable with type sums (α ⊕ β), but might be weird to introduce

def Countable (u : Type*) := (∃ n : Nat, u ~ Fin n) ∨ u ~ ℕ


--The amount of casting that goes on in this proof is hugely uncomfortable but it works...
lemma finitesets0 (n : ℕ) (k : Fin n) : {x // x ≠ k} ~ Fin (n - 1) := by
  induction' n with l hl --induction isn't needed here; hl never gets used. it's just n = 0, n > 0 cases. not worth fixing right now
  exfalso
  exact k.elim0
  rw [Nat.add_one_sub_one]

  let f : { x // x ≠ k } → Fin l → Prop := fun x y => if x = l then y.val = k else x.val = y.val
  use f
  constructor

  intro ⟨x, xneqk⟩ --start of proof that f is a function
  by_cases xl : x = l
  let k' : Fin l := ⟨k.val, by omega⟩ --Have to be able to say k is less than l for the `y.val = k` to even make sense in the function
  use! k'
  constructor
  unfold f
  split_ifs with α --tired of picking letters
  rfl
  rfl
  intro y hy
  unfold f at hy
  rw [if_pos] at hy --apparently `if_pos` can rewrite hy to deduce that we're in the `if` part because that's assumed in `xl`
  ext
  exact hy
  exact xl --ends x=l case
  let x' : Fin l := ⟨x.val, by omega⟩
  use x'
  constructor
  dsimp
  unfold f
  rw [if_neg]
  exact xl
  intro y hy
  unfold f at hy
  rw[if_neg] at hy
  ext
  exact hy.symm
  exact xl --end of proof that f is a function

  constructor
  intro x y c fxc fyc  --begin injective proof
  unfold f at fxc fyc
  split_ifs at fxc with xcase
  split_ifs at fyc with ycase
  ext
  omega --ext omega ext omega ext omega (omega is quite needed for some of the cases, I think there's some weird inequality stuff)
  omega
  split_ifs at fyc with ycase
  ext
  omega
  ext
  omega --end injective proof

  intro y --begin surjective proof
  by_cases hy : y = k.val --need proof l is not k. but since y is k and y ∈ Fin l, this is clear
  let l' : Fin (l+1) := ⟨l,by omega⟩ --omega is just proving l < l+1
  obtain l'nek : l' ≠ k := by
    by_contra --l' = k means y = k, but y ∈ Fin l and that means y < l
    obtain yl : y = l := by
      grind --probably an easy way to close this but I'm going insane
    omega
  use ⟨⟨l,by omega⟩,l'nek⟩
  grind
  let y' : Fin (l+1) := ⟨y.val, by omega⟩
  obtain y'nek : y' ≠ k := by
    by_contra
    grind
  use ⟨⟨y.val,by omega⟩, y'nek⟩
  grind










lemma finitesets1 {u : Type*} (k : u) (n : ℕ) (h: u ~ Fin n) : { x : u // x ≠ k} ~ Fin (n-1) := by
  obtain ⟨f,⟨ff,⟨fi,fs⟩⟩⟩ := h
  induction' n with l hl

  exfalso
  obtain ⟨bad,hbad⟩ := ff k
  exact bad.elim0 --Not exactly sure what elim0 is, but this works

  obtain ⟨m,⟨fkm,fkmu⟩⟩ := ff k
  dsimp at fkmu


--Moving toward the fundamental Theorem 8.1.5 in text. Might need to discuss IsEmpty for empty type first
theorem countable_imp_Natsurj {u : Type*} (h : Countable u) : IsEmpty u ∨ ∃f : Rel ℕ u, isSurjective f := by
  rw [← Not_not (IsEmpty u)] --it was weirdly difficult to get not_not to hit the right thing
  rw [← Imp_iff_not_or, not_isEmpty_iff]
  intro hne
  rcases h with hP | hQ
  obtain k := Classical.choice hne --not Classical.choose, that's for destructuring existence statements
  obtain ⟨n,eq⟩ := hP
  obtain ⟨f,⟨ff,⟨fi,fs⟩⟩⟩ := eq.symm
  --The proof here is to put A in bijection with {0,1,...,|A|-1}, then define f by mapping i to the ith element of A for 0 ≤ i < |A|, and to k otherwise. This is partially baked in already because of the Countable definition using Finset ℕ

  induction' n with l hl
  exfalso
  obtain ⟨⟨a,aemp⟩,ha⟩ := fs k
  contradiction --Empty case of induction finished

  --Assuming you get the surjection when u ~ Fin n, prove you get it when u ~ Fin (n + 1)
  --Need to show: Removing k from u turns f into a bijection between Fin (l+1) without preimage of k and u without k. Then apply induction hypothesis to this new map
  sorry --Finite case finished



  obtain ⟨f,⟨ff,⟨fi,fs⟩⟩⟩ := hQ.symm
  use f --Infinite case finished



/-Equinumerous examples involving ℕ
Notes:
- These require students defining a `Rel`, which they haven't had to do in any other problem. Likely fine with a tutorial

-/

  theorem Nat_eqin_PNat : Nat ~ PNat := by
  let fnp : Rel ℕ PNat := fun a b => b = ⟨a + 1, Nat.succ_pos a⟩ --Without the Nat.succ_pos proof, this has a cast in it. This has a written proof analog; if you want to say something is in ℕ+ you do have to explain why it's greater than zero, so it could be instructive to go through this for cardinalityworld
  use fnp
  constructor
  intro a
  use! ⟨a+1, Nat.succ_pos a⟩
  refine ⟨rfl,?_⟩
  intro y hy
  rw [hy] --end of proof that fnp is a function

  constructor
  intro a b c hac hbc
  --grind closes current goal from here. might be ok?
  unfold fnp at hac hbc
  rw [hac] at hbc
  injection hbc --Extracts the values
  omega --No need to make them prove a + 1 = b + 1 → a = b. Omega works here, originally had grind

  intro y --Is there a way to start with ⟨y,hy⟩ instead & use the inequality to make this less weird at the end?
  use y-1
  unfold fnp
  exact Eq.symm (PNat.succPNat_natPred y) --PNat.succPNat_natPred is the theorem to deal with -1+1 in PNat. Kind of weirdly specific but probably required here

def EvenNat := {n : ℕ // ∃ k : ℕ, n = 2*k}

theorem Nat_eqin_EvenNat : Nat ~ EvenNat := by
  let f : Rel ℕ EvenNat := fun a b => b = ⟨2 * a, by use a⟩
  use f
  constructor
  intro x
  use! ⟨2 * x, by use x⟩
  refine ⟨rfl,?_⟩
  intro y hy
  rw [hy] --end of proof that f is a function

  constructor
  intro a b c hac hbc
  --again, grind works right here. Otherwise, exact same proof at previous one works
  unfold f at hac hbc
  rw [hac] at hbc
  injection hbc
  omega

  intro ⟨y,⟨k,hk⟩⟩ --Grab y and its defining EvenNat property, that is, find k with y = 2k
  use k
  unfold f
  grind --Surely there's a nice way to close this, but nothing I tried worked... `exact hk` doesn't, so it's somehow different from the previous one


--This one requires a complicated piecewise def. It can be defined using division (like the first case being a/2) but then there's a bunch of cast issues; nonetheless, students would be required to type this in , so this might be crazy to ask
theorem Nat_equin_Int : ℕ ~ ℤ := by
  let f : Rel ℕ ℤ := fun a b => by
    by_cases h : Even a
    exact b = (a/2)
    rw [Nat.not_even_iff_odd] at h
    exact b = -(a+1)/2


  use f
  constructor
  intro x
  by_cases hx : Even x
  obtain ⟨k,hk⟩ := id hx
  use! k
  constructor
  grind
  grind
  rw [Nat.not_even_iff_odd] at hx
  obtain ⟨k,hk⟩ := id hx
  use -(k+1)
  grind
  constructor
  intro a b c fac fbc
  grind
  intro y
  rcases Int.nonneg_or_nonneg_neg y with yP | yN
  obtain k := y.toNat
  use k+k
  obtain ek : Even (k+k) := by grind
  unfold f
  split --breaks down the if-then statement

  sorry




--Set not equinumerous to powerset
example (u : Type) : ¬ (u ~ Set u) := by
  rw [Equinumerous, not_exists]
  intro f
  rw [isBijection, and_iff_not_or_not, not_not, ← Imp_iff_not_or]
  intro func
  rw [and_iff_not_or_not,not_not]
  right
  rw [isSurjective]
  push_neg
  let S := { x : u | ∃ p ∈ f.set, p.1 ∉ p.2 ∧ x = p.1 }
  use S
  intro a
  by_cases k: a ∈ S
  intro h
  obtain ⟨p,⟨hp1,hp2,hp3⟩⟩ := id k --id k copies k, then obtain unpacks it
  rw [← hp3] at hp2
  rw [Rel.set] at hp1
  dsimp at hp1
  rw [← hp3] at hp1
  obtain Sp2 := Fun_output_equal f func a S p.2 h hp1
  rw [← Sp2] at hp2
  contradiction
  intro h
  obtain l : a ∈ S := by
    use (a,S)
    refine ⟨h,k,rfl⟩
  contradiction




----------------------Below is old lean function stuff, commented out so I can use Equinumerous and ~ for the stuff above

/-
def Equinumerous (u v : Type*) := ∃ f : u → v, f.Bijective
infix:70 " ~ " => Equinumerous

--Starting to think a subtype tutorial will be needed for this
--This problem feels awkward because the Nat/PNat stuff needed, but maybe it would be natural after a subtype tutorial?
theorem Nat_eqin_PNat : Nat ~ PNat := by
  let fnp : ℕ → PNat := fun a => ⟨a.succ, Nat.succ_pos a⟩ --Is "let" valid in the game? Definition has to be passed a proof that a is positive. Kind of awkward, but makes sense & should probably just be a natural part of cardinality world
  use fnp
  constructor
  intro a b ha
  apply (Nat.succ_inj).mp
  unfold fnp at ha
  injection ha with h --The injection tactic uses that "subtype constructors are injective" to extract the succ equality. Alternatively, grind closes this.
  intro y
  use PNat.natPred y --Grind can't be used to simplify this one, seemingly. Using the more obvious y-1 doesn't help either
  unfold fnp
  unfold PNat.natPred
  exact PNat.succPNat_natPred y

--Equinumerous is an equivalence relation. Uses a few lemmas that could be in Lean Function World

theorem Equinumerous.refl (u : Type*) : u ~ u := by
  use LF_id u
  exact LF_id_bij u

theorem Equinumerous.symm (u v : Type*) : u ~ v → v ~ u := by
  intro h
  obtain ⟨f,hf⟩ := h
  use LF_inv_of_bij f hf
  exact LF_inv_of_bij_bij f hf

theorem Equinumerous.tran (u v w : Type*) : u ~ v → v ~ w → u ~ w := by
  intro huv hvw
  obtain ⟨fuv, hfuv⟩ := huv
  obtain ⟨fvw, hfvw⟩ := hvw
  use fvw ∘ fuv
  refine ⟨LF_comp_inj_of_inj fuv fvw hfuv.left hfvw.left, LF_comp_surj_of_surj fuv fvw hfuv.right hfvw.right⟩

theorem Card_cartprod_equinumerous {a b c d : Type*} (hab : a ~ b) (hcd : c ~ d) : (a × c) ~ (b × d) := by
  obtain ⟨fab, hfab⟩ := hab
  obtain ⟨fcd, hfcd⟩ := hcd
  use fun (x : (a × c))  ↦ ((fab x.1, fcd x.2) : (b × d)) --If you use, for instance, the more natural `(x1,x2) : (a × c)` for the input, the function definition gets bogged down with a `match` definition
  constructor
  intro (x1,x2) (y1,y2) hxy
  rw [Prod.mk_inj] at hxy
  obtain ⟨fabx1y1,fcdx2y2⟩ := hxy
  rw [Prod.mk_inj]
  refine ⟨hfab.left fabx1y1, hfcd.left fcdx2y2⟩ --Ends injective part

  intro (y1,y2)
  obtain ⟨x1,hx1⟩ := hfab.right y1
  obtain ⟨x2,hx2⟩ := hfcd.right y2
  use (x1,x2)
  rw [Prod.mk_inj]
  refine ⟨hx1,hx2⟩




--Type and powerset of type not equinumerous. Not too bad
example (u : Type) : ¬ (u ~ Set u) := by
  rw [Equinumerous]
  push_neg
  intro f
  rw [Function.Bijective, and_iff_not_or_not, not_not]
  right
  rw [Function.Surjective]
  push_neg
  let S : Set u := { a : u | a ∉ f a }
  use S
  intro a
  by_cases k: a ∈ S
  apply Ne.symm (ne_of_mem_of_not_mem' k k) --Closes first case by itself. Maybe this lemma (the ne_of_mem_of_not_mem') could be an earlier set level? Alternatively, grind closes this. But placing grind on the next line finishes the rest of the proof immediately, which might be ok?
  intro h
  obtain l : a ∈ S := by
    rw [← h] at k
    exact k
  exact k l
-/
