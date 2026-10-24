import AFTD.Prelude

/-!
# postage_stamp_number_neg_two_of_odd_not_coprime

Topic: elementary_number_theory   Node: e4fbbdb9f082

Provenance: helper lemma. arXiv:2610.19470 (Positivity and negativity for h-bases for N), Theorem 4.1 and its proof

Integers x, y with a common divisor d ≥ 2 are not coprime.
-/

theorem postage_stamp_number_neg_two_of_odd_not_coprime (x y d : ℤ) (hd : 2 ≤ d) (hx : d ∣ x)
    (hy : d ∣ y) (hc : IsCoprime x y) : False := by
  have := hc.isUnit_of_dvd' hx hy
  rw [Int.isUnit_iff] at this
  omega
