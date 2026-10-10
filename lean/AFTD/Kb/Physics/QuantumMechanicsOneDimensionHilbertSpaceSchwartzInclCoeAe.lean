import AFTD.Prelude
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpace
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceSchwartzIncl
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceToBraApply
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceZeroMemHS
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceZeroFunMemHS
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceELpNormMk

/-!
# QuantumMechanics.OneDimension.HilbertSpace.schwartzIncl_coe_ae

Topic: quantum_mechanics   Node: 014c177e2ae7

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.OneDimension.HilbertSpace.schwartzIncl_coe_ae`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/HilbertSpaces/OneDimension/SchwartzSubmodule.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

QuantumMechanics.OneDimension.HilbertSpace.schwartzIncl_coe_ae
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory in
open SchwartzMap InnerProductSpace in
lemma QuantumMechanics.OneDimension.HilbertSpace.schwartzIncl_coe_ae (ψ : 𝓢(ℝ, ℂ)) :
    ψ.1 =ᶠ[ae volume] (schwartzIncl ψ) := (SchwartzMap.coeFn_toLp _ 2 volume).symm
