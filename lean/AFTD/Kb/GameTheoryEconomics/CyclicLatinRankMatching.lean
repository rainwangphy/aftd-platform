import AFTD.Prelude

/-!
# cyclic_latin_rank_matching

Topic: matching_markets   Node: 58e2f604c713

Provenance: formalization of a published result. Source: Benjamin, Converse, Krieger (1995)

Given a natural number n, an ordering bijection a : Fin n ≃ ZMod n, and an index r : Fin n, cyclic_latin_rank_matching n a r is the matching permutation in Equiv.Perm (ZMod n) sending each man i : ZMod n to woman a r - i.
-/

/-- The monochromatic rank matching pi_r(i) = a_r - i. -/
def cyclic_latin_rank_matching (n : ℕ) (a : Fin n ≃ ZMod n) (r : Fin n) :
    Equiv.Perm (ZMod n) where
  toFun i := a r - i
  invFun j := a r - j
  left_inv i := by simp
  right_inv j := by simp
