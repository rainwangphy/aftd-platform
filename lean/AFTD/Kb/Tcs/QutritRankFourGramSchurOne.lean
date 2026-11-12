import AFTD.Prelude

/-!
# qutrit_rank_four_gram_schur_one

Topic: quantum   Node: b67dc010f5f0

Provenance: helper lemma. Gram-factor helper for the rank-four source in OP-693.

For a rank-four Gram factor with three orthonormal upper rows, a rank-one complement gives a rank-one Schur residual.
-/

open Matrix
open scoped BigOperators Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false

theorem qutrit_rank_four_gram_schur_one
    (U V : Matrix (Fin 3) (Fin 4) ℂ) (w : Fin 4 → ℂ)
    (hcomp : 1 - Uᴴ * U = vecMulVec w (star w)) :
    let B := U * Vᴴ
    let u := V *ᵥ w
    V * Vᴴ = Bᴴ * B + vecMulVec u (star u) := by
  dsimp only
  have hw : V * vecMulVec w (star w) * Vᴴ = vecMulVec (V *ᵥ w) (star (V *ᵥ w)) := by
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]
  calc
    V * Vᴴ = V * ((1 - Uᴴ * U) + Uᴴ * U) * Vᴴ := by simp
    _ = V * (Uᴴ * U) * Vᴴ + V * (1 - Uᴴ * U) * Vᴴ := by
      rw [Matrix.mul_add, Matrix.add_mul, add_comm]
    _ = (U * Vᴴ)ᴴ * (U * Vᴴ) + vecMulVec (V *ᵥ w) (star (V *ᵥ w)) := by
      rw [hcomp, hw, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      simp only [Matrix.mul_assoc]
