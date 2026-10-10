import AFTD.Prelude
import AFTD.Kb.Physics.CosmologyFLRWFriedmannEquationCosmologicalConstantDensity

/-!
# Cosmology.FLRW.FriedmannEquation.cosmologicalConstantPressure

Topic: cosmology   Node: 3b6f050db924

Provenance: formalization of a published result. Source: Physlib, `Cosmology.FLRW.FriedmannEquation.cosmologicalConstantPressure`. Lean proof by Philippe Kevorkian, Jinzheng Li, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Cosmology/FLRW/MatterContent.lean (Copyright (c) 2026 Jinzheng Li. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The pressure `p_Λ = - ρ_Λ c²` associated with the cosmological constant.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Real in
/-- The pressure `p_Λ = - ρ_Λ c²` associated with the cosmological constant. -/
noncomputable def Cosmology.FLRW.FriedmannEquation.cosmologicalConstantPressure (Λ G c : ℝ) : ℝ :=
  -(cosmologicalConstantDensity Λ G c) * c ^ 2
