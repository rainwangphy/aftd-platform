import AFTD.Prelude
import AFTD.Kb.NumberTheory.IntMemHFoldSumset
import AFTD.Kb.NumberTheory.PostageStampIsCoprimeOfMem
import AFTD.Kb.NumberTheory.PostageStampNumberNegTwoOfOddBounds
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# postage_stamp_basis_range_add_two_bounds

Topic: elementary_number_theory   Node: 5af2f3dfa283

Provenance: helper lemma. step towards postage_stamp_basis_range_add_two_le_of_neg_of_odd

If [0, m² + 4m + 1] is contained in the (2m+1)-fold sumset of {a, a+x, a+y} with 0 < x < y and a < 0 (where m ≥ 2), then x and y are coprime, and (2m+1)a satisfies the upper bound (y-1)(1-x) and lower bound (m²+4m+1) - (2m+1)y + (y-1)(y-x-1).
-/

/-- Bounds on (2m+1)a and coprimality when [0, m²+4m+1] is contained in the sumset. -/
theorem postage_stamp_basis_range_add_two_bounds (m : ℕ) (hm : 2 ≤ m) (a x y : ℤ)
    (hx : 0 < x) (hxy : x < y) (ha : a < 0)
    (hsub : ∀ n : ℕ, n ≤ m ^ 2 + 4 * m + 1 → int_mem_h_fold_sumset (2 * m + 1) {a, a + x, a + y} (n : ℤ)) :
    IsCoprime x y ∧
    (2 * (m : ℤ) + 1) * a ≤ (y - 1) * (1 - x) ∧
    (m ^ 2 + 4 * m + 1 : ℤ) - (2 * (m : ℤ) + 1) * y + (y - 1) * (y - x - 1) ≤ (2 * (m : ℤ) + 1) * a := by
  have hR : 2 * m + 1 + 1 ≤ m ^ 2 + 4 * m + 1 := by
    nlinarith
  have hbounds := postage_stamp_number_neg_two_of_odd_bounds m (m ^ 2 + 4 * m + 1) hR a x y hx hxy ha hsub
  rcases hbounds with ⟨hcop, hupper, hlower⟩
  refine ⟨hcop, hupper, ?_⟩
  have hid : (m ^ 2 + 4 * m + 1 : ℤ) - (2 * (m : ℤ) + 1) * y + (y - 1) * (y - x - 1) =
      ((m ^ 2 + 4 * m + 1 : ℕ) : ℤ) - (2 * (m : ℤ) + 2) * y + 1 + (y - 1) * (y - x) := by
    push_cast
    ring
  rw [hid]
  exact hlower
