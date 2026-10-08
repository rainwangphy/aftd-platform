import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityRnDensity

/-!
# CommunicationComplexity.integrable_rnDensity

Topic: information   Node: 02e37ca6ac5c

Provenance: helper lemma. TCSlib, `CommunicationComplexity.integrable_rnDensity`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Integrability of the Radon–Nikodym density. Let $\mu$ and $\nu$ be probability measures on a measurable space $\Omega$, and let
$f\colon \Omega \to \bbr$ be the real-valued Radon–Nikodym density of $\mu$ with respect
to $\nu$, that is, the function whose value at each point $x$ is the real number
obtained from the Radon–Nikodym derivative $\frac{d\mu}{d\nu}(x)$. Then $f$ is
integrable with respect to $\nu$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open ProbabilityTheory in
open scoped ENNReal in
/-- The density `dμ/dν` is `ν`-integrable. -/
theorem CommunicationComplexity.integrable_rnDensity
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    Integrable (rnDensity μ ν) ν := by
  exact
    (Measure.integrable_toReal_rnDeriv
      (μ := μ) (ν := ν))
