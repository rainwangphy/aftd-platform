import AFTD.Prelude

/-!
# helical_point

Topic: combinatorics   Node: eaefd1efbb8d

Provenance: formalization of a published result. Source: arXiv:2610.38368, Theorem 1.1

For a natural number n and an index j : Fin n, helical_point n j is the vector in EuclideanSpace ℝ (Fin 3) with coordinates cos((j : ℝ) / n), sin((j : ℝ) / n), and 2 * (j : ℝ) / n.
-/

/-- The helical point P_j in EuclideanSpace ℝ (Fin 3) with coordinates (cos(j/n), sin(j/n), 2j/n). -/
noncomputable def helical_point (n : ℕ) (j : Fin n) : EuclideanSpace ℝ (Fin 3) :=
  !₂[Real.cos ((j : ℝ) / n), Real.sin ((j : ℝ) / n), 2 * (j : ℝ) / n]
