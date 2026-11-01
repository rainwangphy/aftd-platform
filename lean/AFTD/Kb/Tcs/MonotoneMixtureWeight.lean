import AFTD.Prelude

/-!
# monotoneMixtureWeight

Topic: information   Node: b86221f7b6bb

Provenance: formalization of a published result. Source: arXiv:2610.01563 Lemma 3

For a sequence $P : \mathbb{N}^+ \to \mathbb{R}$, the mixture weight at $k \in \mathbb{N}^+$ is defined by $w_k = k (P(k) - P(k+1))$.
-/

/-- Mixture weight w_k = k(P(k) - P(k+1)) for a sequence on positive integers. -/
noncomputable def monotoneMixtureWeight (P : ℕ+ → ℝ) (k : ℕ+) : ℝ := (k : ℝ) * (P k - P (k + 1))
