import AFTD.Prelude
import AFTD.Kb.Tcs.OneLayeredMaxLayers
import AFTD.Kb.Tcs.OneLayeredLinearBound
import AFTD.Kb.Tcs.OneLayeredBinomialBound
import AFTD.Kb.Tcs.OneLayeredBinomialBoundLePower

/-!
# one_layered_family_upper_bounds

Topic: combinatorics   Node: 3d4808417599

Provenance: formalization of a published result. Source: arXiv:2611.08071 Theorem 2.1

For all integers r ≥ 1 and m ≥ r, the maximum number of layers F(m, r) of a 1-layered family of r-subsets on at most m vertices satisfies F(m, r) ≤ 2^(r - 1) * (m - r) + 1 and F(m, r) ≤ (m - r + 1) * Nat.choose (Nat.log 2 (m - r + 1) + r - 1) (r - 1), and this binomial bound is at most (m - r + 1)^(1 + Real.log r / Real.log 2).
-/

/-- Upper bounds on the number of layers in 1-layered families (Theorem 2.1 of arXiv:2611.08071). -/
theorem one_layered_family_upper_bounds (m r : ℕ) (hr : 1 ≤ r) (hm : r ≤ m) :
    one_layered_max_layers m r ≤ 2 ^ (r - 1) * (m - r) + 1 ∧
    one_layered_max_layers m r ≤ (m - r + 1) * Nat.choose (Nat.log 2 (m - r + 1) + r - 1) (r - 1) ∧
    ((m - r + 1 : ℝ) * ((Nat.log 2 (m - r + 1) + r - 1).choose (r - 1) : ℝ)) ≤
      (m - r + 1 : ℝ) ^ (1 + Real.log (r : ℝ) / Real.log 2) := by
  exact ⟨one_layered_linear_bound m r hr hm, one_layered_binomial_bound m r hr hm,
    one_layered_binomial_bound_le_power m r hr hm⟩
