import AFTD.Prelude
import AFTD.Kb.Tcs.LinearizationCoeff

/-!
# has_property_p

Topic: combinatorics   Node: 4679e3083066

Provenance: formalization of a published result. Source: arXiv:2611.01561 Sec. 2

For N : ℕ and a, b, c : Fin (N + 1) → ℝ, property (P) holds if linearization_coeff N a b c m n k ≥ 0 for all m, n, k : Fin (N + 1).
-/

/-- Property (P): all linearization coefficients are nonnegative. -/
def has_property_p (N : ℕ) (a b c : Fin (N + 1) → ℝ) : Prop := ∀ m n k : Fin (N + 1), 0 ≤ linearization_coeff N a b c m n k
