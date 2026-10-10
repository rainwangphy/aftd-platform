import AFTD.Prelude
import AFTD.Kb.Physics.SUSYN1DeltaContr2
import AFTD.Kb.Physics.SUSYN1DeltaCap2
import AFTD.Kb.Physics.SUSYN1DeltaContr2TmulBasis

/-!
# SUSY.N1.deltaContr₂_unit

Topic: quantum_field_theory   Node: ca0d4ba348bc

Provenance: formalization of a published result. Source: Physlib, `SUSY.N1.deltaContr₂_unit`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/N1/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The snake identity (two-module, `contr_unit` law): contracting `x ∈ M` into the `M`-leg of `deltaCap₂ b' b ∈ N ⊗ M` returns `x`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SUSY SUSY.N1 in
open TensorProduct Module ComplexConjugate in
variable (ι : Type) [Fintype ι] [DecidableEq ι] in
variable {ι} in
variable {M : Type*} [AddCommGroup M] [Module ℂ M] in
variable {N : Type*} [AddCommGroup N] [Module ℂ N] in
/-- The snake identity (two-module, `contr_unit` law): contracting `x ∈ M` into the `M`-leg of `deltaCap₂ b' b ∈ N ⊗ M` returns `x`. -/
lemma SUSY.N1.deltaContr₂_unit (b : Basis ι ℂ M) (b' : Basis ι ℂ N) (x : M) :
    (TensorProduct.lid ℂ M) ((deltaContr₂ b b').rTensor M
      ((TensorProduct.assoc ℂ M N M).symm
        (x ⊗ₜ[ℂ] LinearMap.toSpanSingleton ℂ _ (deltaCap₂ b' b) 1))) = x := by
  rw [LinearMap.toSpanSingleton_apply_one, deltaCap₂, TensorProduct.tmul_sum, map_sum, map_sum,
    map_sum]
  conv_rhs => rw [← b.sum_equivFun x]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [TensorProduct.assoc_symm_tmul, LinearMap.rTensor_tmul, TensorProduct.lid_tmul,
    deltaContr₂_tmul_basis]
