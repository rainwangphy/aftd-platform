import AFTD.Prelude
import AFTD.Kb.Tcs.ClosedNetworkAmGmProductBound

/-!
# closed_network_bound_of_product_bounds

Topic: quantum   Node: a8a2870510bb

Provenance: helper lemma. arXiv:2610.35838 Eq. 32

For any integer n ≥ 1, real correlator values I, J, and non-negative tuples x, y : Fin n → ℝ satisfying x i + y i ≤ 1 for all i, if |I| ≤ ∏ i, x i and |J| ≤ ∏ i, y i, then |I| ^ (1 / n) + |J| ^ (1 / n) ≤ 1.
-/

/-- Bounding the n-th root sum of correlators by the AM-GM product bound. -/
theorem closed_network_bound_of_product_bounds
    (n : ℕ) (hn : 1 ≤ n) (I J : ℝ) (x y : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (hxy : ∀ i, x i + y i ≤ 1)
    (hI : |I| ≤ ∏ i : Fin n, x i) (hJ : |J| ≤ ∏ i : Fin n, y i) :
    |I| ^ (1 / (n : ℝ)) + |J| ^ (1 / (n : ℝ)) ≤ 1 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
  have hz : 0 ≤ 1 / (n : ℝ) := div_nonneg zero_le_one hnpos.le
  have h1 : |I| ^ (1 / (n : ℝ)) ≤ (∏ i : Fin n, x i) ^ (1 / (n : ℝ)) :=
    Real.rpow_le_rpow (abs_nonneg I) hI hz
  have h2 : |J| ^ (1 / (n : ℝ)) ≤ (∏ i : Fin n, y i) ^ (1 / (n : ℝ)) :=
    Real.rpow_le_rpow (abs_nonneg J) hJ hz
  have hmain := closed_network_am_gm_product_bound n hn x y hx hy hxy
  linarith
