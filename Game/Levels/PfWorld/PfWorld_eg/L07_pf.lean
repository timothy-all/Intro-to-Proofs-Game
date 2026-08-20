import Game.Levels.PfWorld.PfWorld_eg.L06_pf

World "PfWorld_eg"
Level 7

Title "Example 7"

Introduction "
### **Level 7**
"

Statement (n : Int) : ( Divides 5 n ∧ Divides 13 n) ↔ Divides 65 n := by
  constructor
  intro h
  obtain ⟨j,hj⟩ := h.left
  obtain ⟨k,hk⟩ := h.right
  obtain hj' : 26 * 5 * j = 26 * n
  rw[← hj]
  simplify
  obtain hk' : 25 * 13 * k = 25 * n
  rw[← hk]
  simplify
  obtain want : n = 26 * 5 * j - 25 * 13 * k
  rw[hj',hk']
  simplify
  use 2 * j - 5 * k
  rw[want]
  simplify
  intro ⟨k,hk⟩
  constructor
  use 13 *k
  rw[← hk]
  simplify
  use 5 * k
  rw[← hk]
  simplify

Conclusion ""
