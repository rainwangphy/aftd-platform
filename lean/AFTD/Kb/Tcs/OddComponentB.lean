import AFTD.Prelude

/-!
# odd_component_b

Topic: combinatorics   Node: fdcff74a60d3

Provenance: formalization of a published result. Source: arXiv:2611.01561 Theorem 4.1

Given a natural number N, coefficients a, c : Fin (2 * N + 1) → ℝ, and an index n : Fin ((N - 1) + 1), the normalized diagonal coefficient of the odd component odd_component_b N a c n is (bn - b0) / a0, where ext_a, ext_c : ℤ → ℝ extend a and c by zero outside [0, 2 * N], a0 = ext_a 1 * ext_a 2, b0 = ext_a 1 * ext_c 2 + ext_c 1 * ext_a 0, and bn = ext_a (2 * n.val + 1) * ext_c (2 * n.val + 2) + ext_c (2 * n.val + 1) * ext_a (2 * n.val).
-/

/-- Normalized diagonal coefficients of the odd component of a symmetric recurrence array of size 2N. -/
noncomputable def odd_component_b (N : ℕ) (a c : Fin (2 * N + 1) → ℝ) (n : Fin ((N - 1) + 1)) : ℝ :=
  let ext_a (k : ℤ) : ℝ := if h : 0 ≤ k ∧ k ≤ 2 * N then a ⟨k.toNat, by omega⟩ else 0
  let ext_c (k : ℤ) : ℝ := if h : 0 ≤ k ∧ k ≤ 2 * N then c ⟨k.toNat, by omega⟩ else 0
  let a0 := ext_a 1 * ext_a 2
  let b0 := ext_a 1 * ext_c 2 + ext_c 1 * ext_a 0
  let bn := ext_a (2 * n.val + 1) * ext_c (2 * n.val + 2) + ext_c (2 * n.val + 1) * ext_a (2 * n.val)
  (bn - b0) / a0
