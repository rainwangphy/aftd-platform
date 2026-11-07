import AFTD.Prelude

/-!
# even_component_c

Topic: combinatorics   Node: 31b9bd8147a4

Provenance: formalization of a published result. Source: arXiv:2611.01561 Theorem 4.1

Given a natural number N, coefficients a, c : Fin (2 * N + 1) → ℝ, and an index n : Fin (N + 1), the normalized downward coefficient of the even component even_component_c N a c n is (ext_c (2 * (n.val : ℤ)) * ext_c (2 * (n.val : ℤ) - 1)) / (ext_a 0 * ext_a 1), where ext_a, ext_c : ℤ → ℝ extend a and c by zero outside [0, 2 * N].
-/

/-- Normalized downward coefficients of the even component of a symmetric recurrence array of size 2N. -/
noncomputable def even_component_c (N : ℕ) (a c : Fin (2 * N + 1) → ℝ) (n : Fin (N + 1)) : ℝ :=
  let ext_a (k : ℤ) : ℝ := if h : 0 ≤ k ∧ k ≤ 2 * N then a ⟨k.toNat, by omega⟩ else 0
  let ext_c (k : ℤ) : ℝ := if h : 0 ≤ k ∧ k ≤ 2 * N then c ⟨k.toNat, by omega⟩ else 0
  let a0 := ext_a 0 * ext_a 1
  (ext_c (2 * (n.val : ℤ)) * ext_c (2 * (n.val : ℤ) - 1)) / a0
