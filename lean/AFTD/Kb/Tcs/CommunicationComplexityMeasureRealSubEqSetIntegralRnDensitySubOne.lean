import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityIntegrableRnDensity
import AFTD.Kb.Tcs.CommunicationComplexityRnDensity

/-!
# CommunicationComplexity.measureReal_sub_eq_setIntegral_rnDensity_sub_one

Topic: information   Node: bbb8f99fca69

Provenance: helper lemma. TCSlib, `CommunicationComplexity.measureReal_sub_eq_setIntegral_rnDensity_sub_one`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Set difference of two measures as an integral of the density minus one. Let $\mu$ and $\nu$ be probability measures on a measurable space $\Omega$ with $\mu$
absolutely continuous with respect to $\nu$ (that is, $\mu \ll \nu$), and let $S
\subseteq \Omega$. Writing $\frac{d\mu}{d\nu}$ for the (real-valued) Radon–Nikodym
derivative of $\mu$ with respect to $\nu$, one has
\[
  \mu(S) - \nu(S) \;=\; \int_{S} \left( \frac{d\mu}{d\nu}(x) - 1 \right) d\nu(x).
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open ProbabilityTheory in
open scoped ENNReal in
/-- If `μ ≪ ν` then for every set `S`, `μ(S) − ν(S) = ∫_S (dμ/dν − 1) dν`. -/
theorem CommunicationComplexity.measureReal_sub_eq_setIntegral_rnDensity_sub_one
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h_ac : μ ≪ ν) (S : Set Ω) :
    μ.real S - ν.real S =
      ∫ x in S, (rnDensity μ ν x - 1) ∂ν := by
  have h_rn_int :
      Integrable (rnDensity μ ν) (ν.restrict S) :=
    (integrable_rnDensity μ ν).mono_measure Measure.restrict_le_self
  have h_one_int :
      Integrable (fun _ : Ω => (1 : ℝ)) (ν.restrict S) :=
    integrable_const 1
  rw [integral_sub h_rn_int h_one_int]
  rw [← Measure.setIntegral_toReal_rnDeriv h_ac S, setIntegral_one_eq_measureReal]
  rfl
