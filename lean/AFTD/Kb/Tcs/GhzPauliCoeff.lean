import AFTD.Prelude

/-!
# ghz_pauli_coeff

Topic: quantum   Node: 3be8abe3d614

Provenance: formalization of a published result. Source: arXiv:2610.35838 Sec. III.2

For an orthonormal frame e of R^3 and index mu in {0, 1, 2, 3}, the Pauli coefficients of A_mu are given by A_0 = I (coefficient 1 at index 0) and A_i = e_{i-1} . sigma for i in {1, 2, 3}.
-/

/-- The expansion coefficients in the Pauli basis of the measurement operator A_mu for frame e. -/
def ghz_pauli_coeff (e : Matrix (Fin 3) (Fin 3) ℝ) (μ : Fin 4) (idx : Fin 4) : ℝ :=
  if μ = 0 then (if idx = 0 then 1 else 0)
  else if idx = 0 then 0
  else e ⟨μ.val - 1, by omega⟩ ⟨idx.val - 1, by omega⟩
