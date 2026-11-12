import AFTD.Prelude

/-!
# qutrit_product_sum_congruence

Topic: quantum   Node: 33784c253c31

Provenance: helper lemma. Product-decomposition helper for OP-693.

A matrix congruence transforms a sum of rank-one operators by transforming each factor.
-/

open Matrix
open scoped BigOperators Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

theorem qutrit_product_sum_congruence
    (F : Matrix (Fin 3) (Fin 3) ℂ) (v : Fin 4 → Fin 3 → ℂ) (c : Fin 4 → ℂ) :
    F * (∑ t, c t • vecMulVec (v t) (star (v t))) * Fᴴ =
      ∑ t, c t • vecMulVec (F *ᵥ v t) (star (F *ᵥ v t)) := by
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  funext t
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]
