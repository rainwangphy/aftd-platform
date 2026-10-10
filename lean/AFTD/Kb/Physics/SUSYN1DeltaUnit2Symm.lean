import AFTD.Prelude
import AFTD.Kb.Physics.SUSYN1DeltaCap2
import AFTD.Kb.Physics.SUSYN1DeltaCap2Comm

/-!
# SUSY.N1.deltaUnit₂_symm

Topic: quantum_field_theory   Node: 1858625d9777

Provenance: formalization of a published result. Source: Physlib, `SUSY.N1.deltaUnit₂_symm`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/N1/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The `unit_symm` law (two-module, `toSpanSingleton` form): `deltaCap₂ b' b` is the swap of `deltaCap₂ b b'`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SUSY SUSY.N1 in
open TensorProduct Module ComplexConjugate in
variable (ι : Type) [Fintype ι] [DecidableEq ι] in
variable {ι} in
variable {M : Type*} [AddCommGroup M] [Module ℂ M] in
variable {N : Type*} [AddCommGroup N] [Module ℂ N] in
omit [DecidableEq ι] in
/-- The `unit_symm` law (two-module, `toSpanSingleton` form): `deltaCap₂ b' b` is the swap of `deltaCap₂ b b'`. -/
lemma SUSY.N1.deltaUnit₂_symm (b : Basis ι ℂ M) (b' : Basis ι ℂ N) :
    LinearMap.toSpanSingleton ℂ _ (deltaCap₂ b' b) 1 =
      LinearMap.lTensor N (LinearEquiv.refl ℂ M).toLinearMap
        (TensorProduct.comm ℂ M N (LinearMap.toSpanSingleton ℂ _ (deltaCap₂ b b') 1)) := by
  simp only [LinearMap.toSpanSingleton_apply_one]
  rw [deltaCap₂_comm]
  simp only [LinearEquiv.refl_toLinearMap, LinearMap.lTensor_id, LinearMap.id_coe, id_eq]
