import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityPinskerInequalityOfAcOfIntegrable
import AFTD.Kb.Tcs.CommunicationComplexityTvDistance

/-!
# CommunicationComplexity.pinsker_inequality_of_ac

Topic: information   Node: 40fbdfd852cf

Provenance: helper lemma. TCSlib, `CommunicationComplexity.pinsker_inequality_of_ac`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Pinsker's inequality under absolute continuity. Let $\mu$ and $\nu$ be probability measures on a measurable space $\Omega$, and suppose
that $\mu$ is absolutely continuous with respect to $\nu$. Then the total variation
distance $\mathrm{TV}(\mu,\nu)$ and the Kullback–Leibler divergence $D_{\mathrm{KL}}(\mu
\,\|\, \nu)$ (both taking values in $[0,\infty]$) satisfy
\[
2\,\mathrm{TV}(\mu,\nu)^2 \le D_{\mathrm{KL}}(\mu \,\|\, \nu).
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open ProbabilityTheory in
open scoped ENNReal in
/-- Pinsker's inequality in `ℝ≥0∞` form under `μ ≪ ν`: `2 · TV(μ, ν)² ≤ KL(μ ‖ ν)`; when the log-likelihood ratio is not integrable the divergence is `∞`. -/
theorem CommunicationComplexity.pinsker_inequality_of_ac
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h_ac : μ ≪ ν) :
    ENNReal.ofReal (2 * tvDistance μ ν ^ 2) ≤
      InformationTheory.klDiv μ ν := by
  by_cases h_int : Integrable (llr μ ν) μ
  · exact pinsker_inequality_of_ac_of_integrable μ ν h_ac h_int
  · rw [InformationTheory.klDiv_of_not_integrable h_int]
    exact le_top
