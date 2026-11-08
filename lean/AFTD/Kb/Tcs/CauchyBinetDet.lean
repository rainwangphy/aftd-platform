import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.CauchyBinet
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cauchy_binet_det

Topic: quantum   Node: 485e39b9f0de

Provenance: formalization of a published result. Source: arXiv:2610.04621 Lemma 5 proof (Appendix B)

For any commutative ring R, natural numbers m and n, and matrices A : Matrix (Fin m) (Fin n) R and B : Matrix (Fin n) (Fin m) R, the determinant of A * B equals the sum over all strictly increasing functions f : Fin m → Fin n of the determinant of the submatrix of A with column indices f multiplied by the determinant of the submatrix of B with row indices f.
-/

/-- The Cauchy-Binet formula for the determinant of the product of two rectangular matrices. -/
theorem cauchy_binet_det {R : Type*} [CommRing R] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin n) (Fin m) R) :
    Matrix.det (A * B) =
      ∑ f ∈ Finset.filter StrictMono (Finset.univ : Finset (Fin m → Fin n)),
        Matrix.det (A.submatrix id f) * Matrix.det (B.submatrix f id) := by
  classical
  rw [cauchyBinet]
  refine Finset.sum_bij
    (fun S _ => S.1.orderEmbOfFin S.2) ?_ ?_ ?_ ?_
  · intro S _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (S.1.orderEmbOfFin S.2).strictMono⟩
  · intro S _ S' _ h
    apply Subtype.ext
    rw [← Finset.image_orderEmbOfFin_univ S.1 S.2,
        ← Finset.image_orderEmbOfFin_univ S'.1 S'.2, h]
  · intro f hf
    rw [Finset.mem_filter] at hf
    refine ⟨⟨Finset.image f Finset.univ, ?_⟩, Finset.mem_univ _, ?_⟩
    · rw [Finset.card_image_of_injective _ hf.2.injective]
      simp
    · exact (Finset.orderEmbOfFin_unique _ (fun x => Finset.mem_image_of_mem f (Finset.mem_univ x)) hf.2).symm
  · intro S _
    rfl
