import AFTD.Prelude

/-!
# recurrence_poly

Topic: combinatorics   Node: 8216a4e499fb

Provenance: formalization of a published result. Source: arXiv:2611.01561 Sec. 2, Eq. (2.2)

The sequence of real polynomials R_n for n : ℕ associated with N : ℕ and a, b, c : Fin (N + 1) → ℝ is defined by R_0 = 1, R_1 = X, and for n = i + 2, R_{i+2} is (1 / a(i+1)) • ((X - b(i+1)) * R_{i+1} - c(i+1) * R_i) when i + 1 < N + 1, and 0 otherwise.
-/

/-- Orthogonal polynomials R_n defined by three-term recurrence. -/
noncomputable def recurrence_poly (N : ℕ) (a b c : Fin (N + 1) → ℝ) :
    ℕ → Polynomial ℝ
| 0 => 1
| 1 => Polynomial.X
| i + 2 =>
  if h : i + 1 < N + 1 then
    (1 / a ⟨i + 1, h⟩) • ((Polynomial.X - Polynomial.C (b ⟨i + 1, h⟩)) * recurrence_poly N a b c (i + 1) -
      Polynomial.C (c ⟨i + 1, h⟩) * recurrence_poly N a b c i)
  else 0
