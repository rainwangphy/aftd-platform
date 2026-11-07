import AFTD.Prelude

/-!
# even_component_a

Topic: combinatorics   Node: d0c70dfeecd9

Provenance: formalization of a published result. Source: arXiv:2611.01561 Theorem 4.1

Given a natural number N, coefficients a : Fin (2 * N + 1) → ℝ, and an index n : Fin (N + 1), the normalized upward coefficient of the even component even_component_a N a n is (ext (2 * n.val) * ext (2 * n.val + 1)) / (ext 0 * ext 1), where ext : ℤ → ℝ extends a by zero outside [0, 2 * N].
-/

/-- Normalized upward coefficients of the even component of a symmetric recurrence array of size 2N. -/
noncomputable def even_component_a (N : ℕ) (a : Fin (2 * N + 1) → ℝ) (n : Fin (N + 1)) : ℝ :=
  let ext (k : ℤ) : ℝ := if h : 0 ≤ k ∧ k ≤ 2 * N then a ⟨k.toNat, by omega⟩ else 0
  let a0 := ext 0 * ext 1
  (ext (2 * n.val) * ext (2 * n.val + 1)) / a0
