import AFTD.Prelude

/-!
# matrix_blow_up_rank

Topic: algebraic_complexity   Node: 7bced21605c0

Provenance: formalization of a published result. Source: arXiv:2611.31963 Section 2.1

For an explicit field F, implicit natural numbers a and b, an arbitrary finite type ι, a natural number k, and a family of rectangular matrices A : ι → Matrix (Fin a) (Fin b) F, matrix_blow_up_rank F k A is the matrix rank over FractionRing (MvPolynomial (ι × Fin k × Fin k) F) of the k-th blow-up matrix ∑ i : ι, (A i mapped into the fraction ring) ⊗ₖ (fun u v => X (i, u, v)).
-/

/-- The rank of the k-th blow-up of a linear symbolic matrix over the fraction field of polynomials in commuting matrix variables. -/
noncomputable def matrix_blow_up_rank (F : Type*) [Field F] {a b : ℕ} {ι : Type*} [Fintype ι] (k : ℕ)
    (A : ι → Matrix (Fin a) (Fin b) F) : ℕ := open scoped Kronecker in
  (∑ i : ι, ((A i).map (algebraMap F (FractionRing (MvPolynomial (ι × Fin k × Fin k) F)))) ⊗ₖ
    (fun u v => algebraMap (MvPolynomial (ι × Fin k × Fin k) F) (FractionRing (MvPolynomial (ι × Fin k × Fin k) F))
      (MvPolynomial.X (i, u, v)))).rank
