import AFTD.Prelude

/-!
# odd_component_a

Topic: combinatorics   Node: 4c0cfaf6917d

Provenance: formalization of a published result. Source: arXiv:2611.01561 Theorem 4.1

Given a natural number N, coefficients a : Fin (2 * N + 1) → ℝ, and an index n : Fin ((N - 1) + 1), the normalized upward coefficient of the odd component odd_component_a N a n is (ext (2 * n.val + 1) * ext (2 * n.val + 2)) / (ext 1 * ext 2), where ext : ℤ → ℝ extends a by zero outside [0, 2 * N].
-/

/-- Normalized upward coefficients of the odd component of a symmetric recurrence array of size 2N. -/
noncomputable def odd_component_a (N : ℕ) (a : Fin (2 * N + 1) → ℝ) (n : Fin ((N - 1) + 1)) : ℝ :=
  let ext (k : ℤ) : ℝ := if h : 0 ≤ k ∧ k ≤ 2 * N then a ⟨k.toNat, by omega⟩ else 0
  let a0 := ext 1 * ext 2
  (ext (2 * n.val + 1) * ext (2 * n.val + 2)) / a0
