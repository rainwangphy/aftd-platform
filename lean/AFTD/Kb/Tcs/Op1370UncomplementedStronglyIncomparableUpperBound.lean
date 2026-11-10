import AFTD.Prelude
import AFTD.Kb.Tcs.IsUncomplemented
import AFTD.Kb.Tcs.StronglyIncomparable
import AFTD.Kb.Tcs.Op1370UpperBoundOfMatrix
import AFTD.Kb.Tcs.HiltonStrongIncomparabilityMatrix

/-!
# op_1370_uncomplemented_strongly_incomparable_upper_bound

Topic: combinatorics   Node: 1b55d542f3d8

Provenance: formalization of a published result. Source: arXiv:2611.12199 Theorem 1.7

Theorem 1.7 of arXiv:2611.12199: for all natural numbers `n` and `t`, if `𝒜 : Fin t → Finset (Finset (Fin n))` is a family such that each `𝒜 i` is uncomplemented and `𝒜` is strongly incomparable, then `∑ i : Fin t, (𝒜 i).card ≤ 2 ^ (n - 1)`.
-/

/-- Theorem 1.7 of arXiv:2611.12199: uncomplemented and strongly incomparable families have total size at most 2^(n-1). -/
theorem op_1370_uncomplemented_strongly_incomparable_upper_bound (n t : ℕ) (𝒜 : Fin t → Finset (Finset (Fin n))) (hunc : ∀ i, is_uncomplemented (𝒜 i)) (hinc : strongly_incomparable 𝒜) : ∑ i, (𝒜 i).card ≤ 2 ^ (n - 1) := by
  exact op_1370_upper_bound_of_matrix n (hilton_strong_incomparability_matrix n) t 𝒜 hunc hinc
