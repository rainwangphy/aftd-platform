import AFTD.Prelude
import AFTD.Kb.Physics.SUSYN1DeltaContr2
import AFTD.Kb.Physics.SUSYN1DeltaCap
import AFTD.Kb.Physics.SUSYN1DeltaCap2
import AFTD.Kb.Physics.SUSYN1DeltaContr2BasisBasis

/-!
# SUSY.N1.deltaContr₂_metric

Topic: quantum_field_theory   Node: a8bb444ae70b

Provenance: formalization of a published result. Source: Physlib, `SUSY.N1.deltaContr₂_metric`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/N1/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The `contr_metric` law (two-module): contracting the inner `M`/`N` legs of `deltaCap b ⊗ deltaCap b'` yields `deltaCap₂ b' b`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SUSY SUSY.N1 in
open TensorProduct Module ComplexConjugate in
variable (ι : Type) [Fintype ι] [DecidableEq ι] in
variable {ι} in
variable {M : Type*} [AddCommGroup M] [Module ℂ M] in
variable {N : Type*} [AddCommGroup N] [Module ℂ N] in
/-- The `contr_metric` law (two-module): contracting the inner `M`/`N` legs of `deltaCap b ⊗ deltaCap b'` yields `deltaCap₂ b' b`. -/
lemma SUSY.N1.deltaContr₂_metric (b : Basis ι ℂ M) (b' : Basis ι ℂ N) :
    (TensorProduct.comm ℂ M N ((TensorProduct.lid ℂ N).lTensor M
      (((deltaContr₂ b b').rTensor N).lTensor M
        (((TensorProduct.assoc ℂ M N N).symm.toLinearMap.lTensor M)
          ((TensorProduct.assoc ℂ M M (N ⊗[ℂ] N))
            (LinearMap.toSpanSingleton ℂ _ (deltaCap b) 1 ⊗ₜ[ℂ]
              LinearMap.toSpanSingleton ℂ _ (deltaCap b') 1)))))) =
      LinearMap.toSpanSingleton ℂ _ (deltaCap₂ b' b) 1 := by
  rw [LinearMap.toSpanSingleton_apply_one, LinearMap.toSpanSingleton_apply_one,
    LinearMap.toSpanSingleton_apply_one]
  conv_lhs => rw [deltaCap, deltaCap, TensorProduct.sum_tmul]
  conv_rhs => rw [deltaCap₂]
  simp only [TensorProduct.tmul_sum, map_sum]
  simp [TensorProduct.assoc_tmul, LinearEquiv.lTensor_tmul, LinearMap.lTensor_tmul,
    TensorProduct.assoc_symm_tmul, LinearMap.rTensor_tmul, TensorProduct.lid_tmul,
    TensorProduct.comm_tmul, deltaContr₂_basis_basis, ite_smul]
  simp [TensorProduct.ite_tmul, Finset.sum_ite_eq]
