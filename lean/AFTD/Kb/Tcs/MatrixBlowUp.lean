import AFTD.Prelude

/-!
# matrix_blow_up

Topic: algebraic_complexity   Node: 84388613e4ab

Provenance: formalization of a published result. Source: arXiv:2611.31963 Section 2.1

For an explicit field F, implicit natural numbers a and b, an arbitrary finite type ι, a natural number k, and a family of rectangular matrices A : ι → Matrix (Fin a) (Fin b) F, matrix_blow_up F k A is the block matrix in Matrix (Fin a × Fin k) (Fin b × Fin k) over FractionRing (MvPolynomial (ι × Fin k × Fin k) F) given by the sum over i : ι of the Kronecker product of (A i mapped into the fraction ring) and the k × k matrix whose (u, v) entry is the variable MvPolynomial.X (i, u, v).
-/

/-- The k-th blow-up of a linear symbolic matrix over the fraction field of polynomials in commuting matrix variables. -/
noncomputable def matrix_blow_up (F : Type*) [Field F] {a b : ℕ} {ι : Type*} [Fintype ι] (k : ℕ)
    (A : ι → Matrix (Fin a) (Fin b) F) :
    Matrix (Fin a × Fin k) (Fin b × Fin k) (FractionRing (MvPolynomial (ι × Fin k × Fin k) F)) := open scoped Kronecker in
  ∑ i : ι, ((A i).map (algebraMap F (FractionRing (MvPolynomial (ι × Fin k × Fin k) F)))) ⊗ₖ
    (fun u v => algebraMap (MvPolynomial (ι × Fin k × Fin k) F) (FractionRing (MvPolynomial (ι × Fin k × Fin k) F))
      (MvPolynomial.X (i, u, v)))
