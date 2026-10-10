import AFTD.Prelude
import AFTD.Kb.Physics.LinearMapMapSmulOfCommutesI

/-!
# ContinuousLinearMap.complexOfCommutesI

Topic: classical_mechanics   Node: 2b9bf68765a8

Provenance: formalization of a published result. Source: Physlib, `ContinuousLinearMap.complexOfCommutesI`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/ComplexLinear.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A continuous `ℝ`-linear map commuting with `i`, as a continuous `ℂ`-linear map.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
/-- A continuous `ℝ`-linear map commuting with `i`, as a continuous `ℂ`-linear map. -/
noncomputable def ContinuousLinearMap.complexOfCommutesI (L : V →L[ℝ] E)
    (h : ∀ v, L (Complex.I • v) = Complex.I • L v) : V →L[ℂ] E where
  toFun := L
  map_add' := L.map_add
  map_smul' c v := LinearMap.map_smul_of_commutesI (L : V →ₗ[ℝ] E) (h v) c
  cont := L.continuous
