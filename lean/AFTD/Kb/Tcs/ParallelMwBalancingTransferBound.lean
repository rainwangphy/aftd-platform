import AFTD.Prelude

/-!
# parallel_mw_balancing_transfer_bound

Topic: combinatorics   Node: 8178d00f71a5

Provenance: helper lemma. Algebraic reduction for parallel_mw_ratio_decreasing_triple and OP-670.

For nonnegative s and A, t at least 2s, B at least A and the stated four cases for d and B, the exact balancing increment satisfies 2(B-A)(sd+t) ≤ Bd(s+t).
-/

theorem parallel_mw_balancing_transfer_bound (s t A B d : ℝ)
    (hs : 0 ≤ s) (ht : 2*s ≤ t) (hA : 0 ≤ A) (hB : A ≤ B)
    (hcases : (d = 1 ∧ B = 2*A) ∨ (d = 2 ∧ B = 4*A) ∨
      (d = 3 ∧ B = 8*A) ∨ 4 ≤ d) :
    2*(B-A)*(s*d+t) ≤ B*d*(s+t) := by
  have ht0 : 0 ≤ t := by linarith
  have hB0 : 0 ≤ B := by linarith
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hd
  · ring_nf; exact le_rfl
  · have hh := mul_nonneg hA (show 0 ≤ t-2*s by linarith)
    nlinarith
  · have hh := mul_nonneg hA (show 0 ≤ t-2*s by linarith)
    have hh2 := mul_nonneg hA hs
    nlinarith
  · have hsub : 0 ≤ d*(s+t)-2*(s*d+t) := by
      have h1 := mul_nonneg (show 0 ≤ d-2 by linarith) (show 0 ≤ t-2*s by linarith)
      have h2 := mul_nonneg (show 0 ≤ d-4 by linarith) hs
      nlinarith
    have h1 := mul_nonneg hB0 hsub
    have h2 := mul_nonneg hA (show 0 ≤ s*d+t by positivity)
    nlinarith
