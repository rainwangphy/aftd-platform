import AFTD.Prelude

/-!
# additive_noise_success_prob

Topic: information   Node: 6ecbe0dab9b5

Provenance: formalization of a published result. Source: arXiv:2611.16066 Proposition 3.1 proof -- Optimal Additive Integer Masks for One-Guess Vulnerability under an Absolute-Moment Budget

The average one-guess success probability of a decision rule g : ℤ → Fin m for a secret with prior p on Fin m under additive noise with distribution q on ℤ is the sum over integers s of p(g(s)) * q(s - g(s)).
-/

/-- Average one-guess success probability of a decision rule under additive noise. -/
noncomputable def additive_noise_success_prob (m : ℕ) (p : Fin m → ℝ) (q : ℤ → ℝ) (g : ℤ → Fin m) : ℝ := ∑' s : ℤ, p (g s) * q (s - g s)
