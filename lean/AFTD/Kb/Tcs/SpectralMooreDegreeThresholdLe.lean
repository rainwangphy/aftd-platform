import AFTD.Prelude
import AFTD.Kb.Tcs.SpectralMooreDegreeThreshold
import AFTD.Kb.Tcs.SpectralMooreMaxOrder

/-!
# spectral_moore_degree_threshold_le

Topic: graphs   Node: ef4320304d79

Provenance: helper lemma. Sanity lemma for spectral_moore_degree_threshold (arXiv:2611.00591 (A spectral Moore problem and the Yang-Koolen conjecture), Question 8.1).

Sanity lemma: K(θ) is at most every degree from which the bound holds.
-/

theorem spectral_moore_degree_threshold_le (θ : ℝ) (K : ℕ)
    (h : ∀ k : ℕ, K ≤ k →
      spectral_moore_max_order k θ ≤ ((2 * k + 2 * ⌊1 + θ ^ 2 / 4⌋₊ : ℕ) : ℕ∞)) :
    spectral_moore_degree_threshold θ ≤ K := by
  exact Nat.sInf_le h
