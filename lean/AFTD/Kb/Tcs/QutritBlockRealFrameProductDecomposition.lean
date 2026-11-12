import AFTD.Prelude

/-!
# qutrit_block_real_frame_product_decomposition

Topic: quantum   Node: d0d4bf22e566

Provenance: helper lemma. Helper for OP-693, in the normal-completion route related to https://arxiv.org/abs/0903.0090.

A real Parseval frame that simultaneously expands a qutrit block and its lower diagonal block yields an explicit four-term product decomposition.
-/

open Matrix
open scoped BigOperators Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

theorem qutrit_block_real_frame_product_decomposition
    (B C : Matrix (Fin 3) (Fin 3) ℂ) (O : Matrix (Fin 3) (Fin 4) ℝ) (lam : Fin 4 → ℂ)
    (hO : O * O.transpose = 1)
    (hB : ∀ i j, B i j = ∑ k, (O i k : ℂ) * lam k * (O j k : ℂ))
    (hC : ∀ i j, C i j = ∑ k, (O i k : ℂ) * (lam k * star (lam k)) * (O j k : ℂ)) :
    ∃ (v : Fin 4 → Fin 3 → ℂ) (a b : Fin 4 → ℂ),
      (∀ t i, star (v t i) = v t i) ∧
      (1 : Matrix (Fin 3) (Fin 3) ℂ) =
        ∑ t, (a t * star (a t)) • vecMulVec (v t) (star (v t)) ∧
      B = ∑ t, (a t * star (b t)) • vecMulVec (v t) (star (v t)) ∧
      C = ∑ t, (b t * star (b t)) • vecMulVec (v t) (star (v t)) := by
  refine ⟨fun t i => (O i t : ℂ), fun _ => 1, fun t => star (lam t), ?_, ?_, ?_, ?_⟩
  · intro t i
    simp
  · ext i j
    have hr := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M i j) hO
    simp only [Matrix.mul_apply, Matrix.transpose_apply] at hr
    have hc : (∑ k, (O i k : ℂ) * (O j k : ℂ)) = ((1 : Matrix (Fin 3) (Fin 3) ℝ) i j : ℂ) := by
      exact_mod_cast hr
    by_cases hij : i = j <;>
      simpa [hij, Matrix.vecMulVec_apply, Matrix.one_apply, Matrix.sum_apply, Matrix.smul_apply,
        mul_comm, mul_left_comm, mul_assoc] using hc.symm
  · ext i j
    simpa [Matrix.vecMulVec_apply, Matrix.sum_apply, Matrix.smul_apply,
      mul_comm, mul_left_comm, mul_assoc] using hB i j
  · ext i j
    simpa [Matrix.vecMulVec_apply, Matrix.sum_apply, Matrix.smul_apply,
      mul_comm, mul_left_comm, mul_assoc] using hC i j
