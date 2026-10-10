import AFTD.Prelude

/-!
# Cosmology.FLRW.FriedmannEquation.cosmologicalConstantDensity

Topic: cosmology   Node: 0e5b2047caf1

Provenance: formalization of a published result. Source: Physlib, `Cosmology.FLRW.FriedmannEquation.cosmologicalConstantDensity`. Lean proof by Philippe Kevorkian, Jinzheng Li, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Cosmology/FLRW/MatterContent.lean (Copyright (c) 2026 Jinzheng Li. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The density `ρ_Λ = Λ c² / (8 π G)` associated with the cosmological constant.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Real in
/-- The density `ρ_Λ = Λ c² / (8 π G)` associated with the cosmological constant. -/
noncomputable def Cosmology.FLRW.FriedmannEquation.cosmologicalConstantDensity (Λ G c : ℝ) : ℝ :=
  Λ * c ^ 2 / (8 * π * G)
