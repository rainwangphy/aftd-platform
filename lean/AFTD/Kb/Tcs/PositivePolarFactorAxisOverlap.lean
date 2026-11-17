import AFTD.Prelude

/-!
# positive_polar_factor_axis_overlap

Topic: quantum   Node: c503073b292d

Provenance: helper lemma. arXiv:2611.19367v1, Lemma 3, Eq. (29).

An orthogonal image of a nonzero vector has positive dot product with the image of that vector under a positive definite polar factor.
-/

theorem positive_polar_factor_axis_overlap (O P : Matrix (Fin 3) (Fin 3) ℝ) (r : Fin 3 → ℝ) (hO : O.transpose * O = 1) (hP : P.PosDef) (hr : r ≠ 0) : let b := O.mulVec r; let x := O.mulVec (P.mulVec r); 0 < ∑ i, b i * x i := by
  dsimp only
  change 0 < (O.mulVec r) ⬝ᵥ (O.mulVec (P.mulVec r))
  have hpos : 0 < r ⬝ᵥ P.mulVec r := by
    simpa using (Matrix.posDef_iff_dotProduct_mulVec.mp hP).2 hr
  have hmv : O.transpose.mulVec (O.mulVec (P.mulVec r)) = P.mulVec r := by
    rw [Matrix.mulVec_mulVec, hO, Matrix.one_mulVec]
  calc
    (O.mulVec r) ⬝ᵥ (O.mulVec (P.mulVec r))
        = r ⬝ᵥ P.mulVec r := by
          rw [dotProduct_comm (O.mulVec r) (O.mulVec (P.mulVec r))]
          rw [← Matrix.dotProduct_transpose_mulVec O r (O.mulVec (P.mulVec r))]
          rw [hmv]
    _ > 0 := hpos
