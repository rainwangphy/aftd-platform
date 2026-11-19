import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SampfordRareGroupWeight

/-!
# sampfordRareGroupRatio

Topic: social_choice   Node: 49b042d2e1eb

Provenance: formalization of a published result. Source: OP-1944

For partition parameters m, r, k with m + r = n, r ≥ 2, 1 ≤ k < m, the rare-group coupling deficit ratio is the quotient of the sum of weights W_ℓ for ℓ ≥ 2 over the total sum of weights W_ℓ for ℓ ≥ 0.
-/

/-- The rare-group coupling deficit ratio sum_{ℓ ≥ 2} W_ℓ / sum_{ℓ ≥ 0} W_ℓ. -/
noncomputable def sampfordRareGroupRatio (m r k : ℕ) : ℝ :=
  (∑ ℓ ∈ Finset.Ico 2 (k + 2), sampfordRareGroupWeight m r k ℓ) /
  (∑ ℓ ∈ Finset.range (k + 2), sampfordRareGroupWeight m r k ℓ)
