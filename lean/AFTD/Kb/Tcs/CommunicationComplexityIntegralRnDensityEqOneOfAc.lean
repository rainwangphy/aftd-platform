import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityRnDensity

/-!
# CommunicationComplexity.integral_rnDensity_eq_one_of_ac

Topic: information   Node: f508fb156ad1

Provenance: helper lemma. TCSlib, `CommunicationComplexity.integral_rnDensity_eq_one_of_ac`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Integral of the Radon–Nikodym derivative equals one. Let $\mu$ and $\nu$ be probability measures on a measurable space $\Omega$, and suppose
that $\mu$ is absolutely continuous with respect to $\nu$, written $\mu \ll \nu$. Then
the Radon–Nikodym derivative $\frac{d\mu}{d\nu}$ integrates to one against $\nu$:
\[
  \int_{\Omega} \frac{d\mu}{d\nu}(x)\,d\nu(x) = 1.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open ProbabilityTheory in
open scoped ENNReal in
/-- If `μ ≪ ν` then the density `dμ/dν` integrates to `1` against `ν` (both are probability measures). -/
theorem CommunicationComplexity.integral_rnDensity_eq_one_of_ac
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h_ac : μ ≪ ν) :
    ∫ x, rnDensity μ ν x ∂ν = 1 := by
  have h := Measure.integral_toReal_rnDeriv h_ac
  simpa [rnDensity] using h
