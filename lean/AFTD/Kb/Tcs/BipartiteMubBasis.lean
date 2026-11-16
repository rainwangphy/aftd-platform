import AFTD.Prelude

/-!
# bipartite_mub_basis

Topic: quantum   Node: 695c1cfa2541

Provenance: formalization of a published result. Source: arXiv:2611.18232 Thm. 4, Eq. (33)

The family of p+1 bases in EuclideanSpace ℂ (Fin (p * q)) constructed in arXiv:2611.18232: for k = 0 and t : Fin (p * q), it is the computational basis vector EuclideanSpace.basisFun (Fin (p * q)) ℂ t; for k ≠ 0, it is the vector in EuclideanSpace ℂ (Fin (p * q)) whose n-th coordinate (for n : Fin (p * q)) equals (1 / Real.sqrt (p * q : ℝ) : ℂ) * Complex.exp (Complex.I * Real.pi * (((p : ℤ) + (q : ℤ)) * ((k.val : ℤ) * (n.val : ℤ)^2 - 2 * (t.val : ℤ) * (n.val : ℤ)) : ℂ) * ((p * q : ℂ) + 1) / (p * q : ℂ)).
-/

/-- The p+1 mutually unbiased bases in dimension pq constructed in arXiv:2611.18232. -/
noncomputable def bipartite_mub_basis (p q : ℕ) (k : Fin (p + 1)) (t : Fin (p * q)) :
    EuclideanSpace ℂ (Fin (p * q)) :=
  if k = 0 then
    EuclideanSpace.basisFun (Fin (p * q)) ℂ t
  else
    let d : ℕ := p * q
    let coeff : ℂ := (1 : ℂ) / (Real.sqrt (d : ℝ) : ℂ)
    (WithLp.equiv 2 _).symm fun n : Fin (p * q) =>
      let n_val : ℤ := (n.val : ℤ)
      let t_val : ℤ := (t.val : ℤ)
      let r_val : ℤ := (k.val : ℤ)
      let exponent : ℤ := ((p : ℤ) + (q : ℤ)) * (r_val * n_val ^ 2 - 2 * t_val * n_val)
      coeff * Complex.exp (Complex.I * Real.pi * (exponent : ℂ) * ((d : ℂ) + 1) / (d : ℂ))
