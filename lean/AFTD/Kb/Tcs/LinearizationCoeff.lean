import AFTD.Prelude
import AFTD.Kb.Tcs.RecurrenceMatrix
import AFTD.Kb.Tcs.RecurrencePoly

/-!
# linearization_coeff

Topic: combinatorics   Node: d649597ab60e

Provenance: formalization of a published result. Source: arXiv:2611.01561 Sec. 2, Lemma 2.1

For N : ℕ, a, b, c : Fin (N + 1) → ℝ, and m, n, k : Fin (N + 1), the linearization coefficient is the (n, k) entry of the matrix polynomial evaluating recurrence_poly N a b c m.val at recurrence_matrix N a b c.
-/

/-- Linearization coefficient g(m, n; k) = [R_m(J)]_{n, k}. -/
noncomputable def linearization_coeff (N : ℕ) (a b c : Fin (N + 1) → ℝ)
    (m n k : Fin (N + 1)) : ℝ := (Polynomial.aeval (recurrence_matrix N a b c) (recurrence_poly N a b c m.val)) n k
