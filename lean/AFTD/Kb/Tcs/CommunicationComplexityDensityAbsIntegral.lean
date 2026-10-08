import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityRnDensity

/-!
# CommunicationComplexity.densityAbsIntegral

Topic: information   Node: aac54e214187

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.densityAbsIntegral`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The quantity $\mathrm{densityAbsIntegral}(\mu,\nu) := \int |\mathrm{rnDensity}(\mu,\nu)(x) - 1|\,d\nu$ is the $L^1(\nu)$-distance of the Radon-Nikodym density from $1$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open ProbabilityTheory in
open scoped ENNReal in
/-- The `L¹` distance `∫ |dμ/dν − 1| dν` between the density and the constant `1`. -/
noncomputable def CommunicationComplexity.densityAbsIntegral
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : ℝ :=
  ∫ x, |rnDensity μ ν x - 1| ∂ν
