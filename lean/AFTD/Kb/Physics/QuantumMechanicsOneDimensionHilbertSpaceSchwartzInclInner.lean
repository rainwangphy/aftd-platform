import AFTD.Prelude
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpace
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceSchwartzIncl
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceSchwartzInclCoeAe
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceToBraApply
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceZeroMemHS
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceZeroFunMemHS
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceELpNormMk

/-!
# QuantumMechanics.OneDimension.HilbertSpace.schwartzIncl_inner

Topic: quantum_mechanics   Node: ca7e9c544d05

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.OneDimension.HilbertSpace.schwartzIncl_inner`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/HilbertSpaces/OneDimension/SchwartzSubmodule.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

QuantumMechanics.OneDimension.HilbertSpace.schwartzIncl_inner
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory in
open SchwartzMap InnerProductSpace in
lemma QuantumMechanics.OneDimension.HilbertSpace.schwartzIncl_inner (ψ1 ψ2 : 𝓢(ℝ, ℂ)) :
    ⟪schwartzIncl ψ1, schwartzIncl ψ2⟫_ℂ = ∫ x : ℝ, starRingEnd ℂ (ψ1 x) * ψ2 x := by
  apply MeasureTheory.integral_congr_ae
  have h1 : ψ1.1 =ᶠ[ae volume] (schwartzIncl ψ1) :=
    schwartzIncl_coe_ae ψ1
  have h2 : ψ2.1 =ᶠ[ae volume] (schwartzIncl ψ2) :=
    schwartzIncl_coe_ae ψ2
  filter_upwards [h1, h2] with _ h1 h2
  rw [← h1, ← h2]
  simp only [RCLike.inner_apply]
  rw [mul_comm]
  rfl
