import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityRealPinskerInequalityOfAcOfIntegrable
import AFTD.Kb.Tcs.CommunicationComplexityTvDistance

/-!
# CommunicationComplexity.pinsker_inequality_of_ac_of_integrable

Topic: information   Node: ba2760d2182b

Provenance: helper lemma. TCSlib, `CommunicationComplexity.pinsker_inequality_of_ac_of_integrable`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Pinsker's inequality under absolute continuity. Let $\mu$ and $\nu$ be probability measures on a measurable space $\Omega$, and suppose
$\mu$ is absolutely continuous with respect to $\nu$ and that the log-likelihood ratio
$\log\frac{d\mu}{d\nu}$ is $\mu$-integrable. Then, as an inequality in the extended
nonnegative reals $\bbr_{\ge 0} \cup \{\infty\}$,
\[
  2\,\mathrm{TV}(\mu,\nu)^2 \;\le\; \mathrm{KL}(\mu \,\|\, \nu),
\]
where $\mathrm{TV}(\mu,\nu)$ is the total variation distance between $\mu$ and $\nu$ and
$\mathrm{KL}(\mu \,\|\, \nu)$ is the Kullback–Leibler divergence of $\mu$ from $\nu$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open ProbabilityTheory in
open scoped ENNReal in
/-- Pinsker's inequality in `ℝ≥0∞` form under `μ ≪ ν` and integrability of the log-likelihood ratio: `2 · TV(μ, ν)² ≤ KL(μ ‖ ν)`. -/
theorem CommunicationComplexity.pinsker_inequality_of_ac_of_integrable
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h_ac : μ ≪ ν)
    (h_int : Integrable (llr μ ν) μ) :
    ENNReal.ofReal (2 * tvDistance μ ν ^ 2) ≤
      InformationTheory.klDiv μ ν := by
  rw [InformationTheory.klDiv_of_ac_of_integrable h_ac h_int]
  apply ENNReal.ofReal_le_ofReal
  have h_real := real_pinsker_inequality_of_ac_of_integrable μ ν h_ac h_int
  simpa using h_real
