import AFTD.Prelude
import AFTD.Kb.Tcs.SpectralMooreDegreeThreshold
import AFTD.Kb.Tcs.SpectralMooreMaxOrder

/-!
# spectral_moore_degree_threshold_spec

Topic: graphs   Node: c4c2085f3e5b

Provenance: helper lemma. Sanity lemma for spectral_moore_degree_threshold (arXiv:2611.00591 (A spectral Moore problem and the Yang-Koolen conjecture), Question 8.1).

Sanity lemma: if some degree threshold exists, the bound v(k, θ) ≤ 2k + 2⌊1 + θ²/4⌋ holds for every k ≥ K(θ).
-/

theorem spectral_moore_degree_threshold_spec (θ : ℝ)
    (h : ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      spectral_moore_max_order k θ ≤ ((2 * k + 2 * ⌊1 + θ ^ 2 / 4⌋₊ : ℕ) : ℕ∞)) :
    ∀ k : ℕ, spectral_moore_degree_threshold θ ≤ k →
      spectral_moore_max_order k θ ≤ ((2 * k + 2 * ⌊1 + θ ^ 2 / 4⌋₊ : ℕ) : ℕ∞) := by
  exact Nat.sInf_mem h
