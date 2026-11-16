import AFTD.Prelude

/-!
# truncated_geometric_distribution

Topic: information   Node: c4a525690c07

Provenance: helper lemma. step towards biased_bit_optimal_mask_unique

The truncated geometric distribution T_{L, k}(s) with base parameter a, shift L ∈ ℤ, and length k ∈ ℕ is defined as (1 - a) * a^(s - L) / (1 - a^k) for L ≤ s < L + k, and 0 otherwise.
-/

/-- The truncated geometric distribution T_{L, k}(s) with base parameter a, shift L ∈ ℤ, and length k ∈ ℕ is defined as (1 - a) * a^(s - L) / (1 - a^k) for L ≤ s < L + k, and 0 otherwise. -/
noncomputable def truncated_geometric_distribution (a : ℝ) (L : ℤ) (k : ℕ) (s : ℤ) : ℝ := if L ≤ s ∧ s < L + k then (1 - a) * a ^ (s - L) / (1 - a ^ k) else 0
