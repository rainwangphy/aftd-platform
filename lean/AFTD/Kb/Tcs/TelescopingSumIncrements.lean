import AFTD.Prelude

/-!
# telescoping_sum_increments

Topic: combinatorics   Node: 2b643f2a0161

Provenance: helper lemma. arXiv:2611.19312, Section 4, proof of Theorem 3 (iv)

For any sequence f : ℕ → ℝ and any integer r ≥ 3, the sum of consecutive increments Δ t = f (t + 1) - f t from t = 1 to r - 3 telescopes to f (r - 2) - f 1.
-/

open BigOperators in
/-- Telescoping sum of consecutive increments from 1 to r - 3. -/
theorem telescoping_sum_increments (f : ℕ → ℝ) (r : ℕ) (hr : 3 ≤ r) :
    let Δ : ℕ → ℝ := fun t => f (t + 1) - f t
    ∑ t ∈ Finset.Icc 1 (r - 3), Δ t = f (r - 2) - f 1 := by
  intro Δ
  by_cases hr3 : r = 3
  · subst r
    simp
  · have h1 : 1 ≤ r - 3 := by
      apply Nat.le_sub_of_add_le
      have hlt : 3 < r := lt_of_le_of_ne hr (Ne.symm hr3)
      exact Nat.succ_le_of_lt hlt
    have h2 : r - 3 + 1 = r - 2 := by omega
    rw [Finset.sum_Icc_sub h1, h2]
