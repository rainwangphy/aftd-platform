import AFTD.Prelude

/-!
# sampfordRareGroupWeight

Topic: social_choice   Node: c0bdd0eee07e

Provenance: formalization of a published result. Source: OP-1944

For integers m, r, k, ℓ with m + r = n, r ≥ 2, 1 ≤ k < m, the rare-group weight W_ℓ is defined as binom(m, k + 1 - ℓ) * binom(r, ℓ) * [k / (m - k)]^(k + 1 - ℓ) * [1 / (r - 1)]^ℓ * [(k + 1 - ℓ)(1 - k / m) + ℓ(1 - 1 / r)] for ℓ ≤ k + 1, and 0 for out-of-range indices.
-/

/-- The rare-group weight W_ℓ from the Sampford coupling obstruction frontier. -/
noncomputable def sampfordRareGroupWeight (m r k ℓ : ℕ) : ℝ :=
  if ℓ ≤ k + 1 then
    (Nat.choose m (k + 1 - ℓ) : ℝ) * (Nat.choose r ℓ : ℝ) *
    ((k : ℝ) / (m - k : ℝ)) ^ (k + 1 - ℓ) * ((1 : ℝ) / (r - 1 : ℝ)) ^ ℓ *
    ((k + 1 - ℓ : ℝ) * (1 - (k : ℝ) / m) + (ℓ : ℝ) * (1 - (1 : ℝ) / r))
  else 0
