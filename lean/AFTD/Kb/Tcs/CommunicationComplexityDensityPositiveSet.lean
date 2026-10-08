import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityRnDensity

/-!
# CommunicationComplexity.densityPositiveSet

Topic: information   Node: 0c2d2c5aa180

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.densityPositiveSet`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The \emph{density positive set} is $\{x \in \Omega : \mathrm{rnDensity}(\mu,\nu)(x) \ge 1\}$,
the region where $\mu$ locally dominates $\nu$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open ProbabilityTheory in
open scoped ENNReal in
/-- The set `{dμ/dν ≥ 1}` on which `μ` has at least as much density as `ν`. -/
def CommunicationComplexity.densityPositiveSet
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : Set Ω :=
  {x | 1 ≤ rnDensity μ ν x}
