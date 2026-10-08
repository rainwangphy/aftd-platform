import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityRnDensity

/-!
# CommunicationComplexity.measurable_rnDensity

Topic: information   Node: 306ca1bf40be

Provenance: helper lemma. TCSlib, `CommunicationComplexity.measurable_rnDensity`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Measurability of the Radon–Nikodym density. Let $\mu$ and $\nu$ be probability measures on a measurable space $\Omega$, and consider
the real-valued Radon–Nikodym density $x \mapsto \left(\tfrac{d\mu}{d\nu}(x)\right)$,
obtained from the $[0,\infty]$-valued Radon–Nikodym derivative $\tfrac{d\mu}{d\nu}\colon
\Omega \to [0,\infty]$ by taking its real value at each point. Then this function
$\Omega \to \bbr$ is measurable.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open ProbabilityTheory in
open scoped ENNReal in
/-- The density `dμ/dν` is measurable. -/
theorem CommunicationComplexity.measurable_rnDensity
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    Measurable (rnDensity μ ν) := by
  unfold rnDensity
  fun_prop
