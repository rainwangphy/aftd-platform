import AFTD.Prelude

/-!
# scoring_norm_one

Topic: social_choice   Node: eaffdd854b61

Provenance: formalization of a published result. Source: arXiv:2610.26535 Definition 2

The 1-norm of a scoring vector s in Q^m is the sum of its entries.
-/

/-- The 1-norm (sum of entries) of a scoring vector. -/
def scoring_norm_one {m : ℕ} (s : Fin m → ℚ) : ℚ :=
  ∑ i : Fin m, s i
