import AFTD.Prelude
import AFTD.Kb.Tcs.SpectralMooreMaxOrder

/-!
# spectral_moore_degree_threshold

Topic: graphs   Node: 331e58aad1c9

Provenance: formalization of a published result. Source: arXiv:2611.00591 (A spectral Moore problem and the Yang-Koolen conjecture), Question 8.1 (the threshold K(θ) whose value the question asks for); degrees range over ℕ, so the least K is taken in ℕ.

K(θ): the least natural number K such that v(k, θ) ≤ 2k + 2⌊1 + θ²/4⌋ for every degree k ≥ K (defaulting to 0 if there is no such K).
-/

/-- `K(θ)`: the least degree `K` such that `v(k, θ) ≤ 2k + 2⌊1 + θ²/4⌋` for every degree `k ≥ K` (`0` if no such `K` exists; for `θ ≥ 1` one exists by Theorem 5.4 of arXiv:2611.00591). -/
noncomputable def spectral_moore_degree_threshold (θ : ℝ) : ℕ :=
  sInf {K : ℕ | ∀ k : ℕ, K ≤ k →
    spectral_moore_max_order k θ ≤ ((2 * k + 2 * ⌊1 + θ ^ 2 / 4⌋₊ : ℕ) : ℕ∞)}
