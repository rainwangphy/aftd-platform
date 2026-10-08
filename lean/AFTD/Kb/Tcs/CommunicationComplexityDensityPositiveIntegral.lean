import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDensityPositiveSet
import AFTD.Kb.Tcs.CommunicationComplexityRnDensity

/-!
# CommunicationComplexity.densityPositiveIntegral

Topic: information   Node: 51546e74e16b

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.densityPositiveIntegral`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The \emph{density positive integral} is
$\mathrm{densityPositiveIntegral}(\mu,\nu) := \int_{\mathrm{densityPositiveSet}} (\mathrm{rnDensity}(\mu,\nu)(x)-1)\,d\nu$,
the excess mass of $\mu$ over $\nu$ on the region where $\mu$ dominates.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open ProbabilityTheory in
open scoped ENNReal in
/-- The positive part `∫_{dμ/dν ≥ 1} (dμ/dν − 1) dν` of the centred density. -/
noncomputable def CommunicationComplexity.densityPositiveIntegral
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : ℝ :=
  ∫ x in densityPositiveSet μ ν, (rnDensity μ ν x - 1) ∂ν
