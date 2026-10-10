import AFTD.Prelude
import AFTD.Kb.Physics.MSSMACCsAccQuadExt
import AFTD.Kb.Tcs.BoolFourierFourierCoeffConvolution

/-!
# LinearPMap.inner_map_polarization'

Topic: quantum_mechanics   Node: 35b969b3086e

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.inner_map_polarization'`. Lean proof by Adam Bornemann, Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Unbounded.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The analogue of `inner_map_polarization'` for LinearPMap.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Submodule in
open InnerProductSpace in
open Complex ComplexConjugate in
variable
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {H'' : Type*} [NormedAddCommGroup H''] [InnerProductSpace ℂ H'']
  {α : Type*} [Fintype α]
  {T T₁ T₂ : H →ₗ.[ℂ] H} {S : α → H →ₗ.[ℂ] H}
  {U U₁ U₂ : H →ₗ.[ℂ] H'} {W : α → H →ₗ.[ℂ] H'}
  {V V₁ V₂ : H' →ₗ.[ℂ] H''} in
variable (u : H ≃ₗᵢ[ℂ] H') (A : H →ₗ.[ℂ] H) in
variable {u A} in
/-- The analogue of `inner_map_polarization'` for LinearPMap. -/
theorem LinearPMap.inner_map_polarization' (x y : T.domain) :
    ⟪T x, y⟫_ℂ = (⟪T (x + y), ↑(x + y)⟫_ℂ - ⟪T (x - y), ↑(x - y)⟫_ℂ
      - I * ⟪T (x + I • y), ↑(x + I • y)⟫_ℂ + I * ⟪T (x - I • y), ↑(x - I • y)⟫_ℂ) / 4 := by
  simp only [map_add, coe_add, inner_add_right, inner_add_left, map_sub, AddSubgroupClass.coe_sub,
    inner_sub_right, inner_sub_left, sub_sub, map_smul, SetLike.val_smul, inner_smul_left, conj_I,
    neg_mul, inner_smul_right, mul_add, mul_neg, ← mul_assoc, ← pow_two, I_sq, one_mul, neg_neg,
    sub_neg_eq_add, mul_sub]
  ring

-- The analogue of `LinearMap.isSymmetric_iff_inner_map_self_real` for LinearPMap.
