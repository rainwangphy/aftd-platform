import AFTD.Prelude

/-!
# candidate_density_matrix

Topic: quantum_mechanics   Node: 515502deafce

Provenance: formalization of a published result. Source: OP-1552; arXiv:2409.01966

For real numbers p and q, candidate_density_matrix p q is the complex matrix indexed by (Fin 2 × Fin 2) × (Fin 2 × Fin 2) whose entry at ((a1, b1), (a2, b2)) is p * q if (a1, b1) = (0, 0) and (a2, b2) = (0, 0); p * Real.sqrt (q * (1 - q)) if ((a1, b1) = (0, 0) and (a2, b2) = (1, 1)) or ((a1, b1) = (1, 1) and (a2, b2) = (0, 0)); p * (1 - q) if (a1, b1) = (1, 1) and (a2, b2) = (1, 1); 1 - p if (a1, b1) = (0, 1) and (a2, b2) = (0, 1); and 0 otherwise.
-/

/-- The two-parameter rank-at-most-two complex matrix candidate_density_matrix p q indexed by (Fin 2 × Fin 2). -/
noncomputable def candidate_density_matrix (p q : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := Matrix.of fun (a1, b1) (a2, b2) =>
    if (a1, b1) = (0, 0) ∧ (a2, b2) = (0, 0) then (p * q : ℂ)
    else if (a1, b1) = (0, 0) ∧ (a2, b2) = (1, 1) then (p * Real.sqrt (q * (1 - q)) : ℂ)
    else if (a1, b1) = (1, 1) ∧ (a2, b2) = (0, 0) then (p * Real.sqrt (q * (1 - q)) : ℂ)
    else if (a1, b1) = (1, 1) ∧ (a2, b2) = (1, 1) then (p * (1 - q) : ℂ)
    else if (a1, b1) = (0, 1) ∧ (a2, b2) = (0, 1) then (1 - p : ℂ)
    else 0
