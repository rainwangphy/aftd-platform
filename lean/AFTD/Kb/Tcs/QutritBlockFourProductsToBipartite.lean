import AFTD.Prelude

/-!
# qutrit_block_four_products_to_bipartite

Topic: quantum   Node: 162e2bfd0149

Provenance: helper lemma. Product-decomposition helper for OP-693.

The four spectral block sums combine into a four-product bipartite matrix.
-/

open Matrix
open scoped BigOperators Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

theorem qutrit_block_four_products_to_bipartite
    (B C : Matrix (Fin 3) (Fin 3) ℂ)
    (v : Fin 4 → Fin 3 → ℂ) (a b : Fin 4 → ℂ)
    (hv : ∀ t i, star (v t i) = v t i)
    (h0 : (1 : Matrix (Fin 3) (Fin 3) ℂ) =
      ∑ t, (a t * star (a t)) • vecMulVec (v t) (star (v t)))
    (hB : B = ∑ t, (a t * star (b t)) • vecMulVec (v t) (star (v t)))
    (hC : C = ∑ t, (b t * star (b t)) • vecMulVec (v t) (star (v t))) :
    ∀ (i j : Fin 3) (p q : Fin 2),
      (if p = 0 then if q = 0 then (1 : Matrix (Fin 3) (Fin 3) ℂ) i j else B i j
       else if q = 0 then Bᴴ i j else C i j) =
      ∑ t, (v t i * ![a t, b t] p) * star (v t j * ![a t, b t] q) := by
  intro i j p q
  have h0' := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M i j) h0
  have hB' := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M i j) hB
  have hC' := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M i j) hC
  have hBt := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M j i) hB
  fin_cases p <;> fin_cases q
  · simpa [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, hv,
      smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using h0'
  · simpa [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, hv,
      smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hB'
  · have hBt' := congrArg star hBt
    simpa [Matrix.conjTranspose_apply, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, star_sum, hv, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc] using hBt'
  · simpa [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, hv,
      smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hC'
