import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityFiniteProbabilitySpace

/-!
# CommunicationComplexity.FiniteProbabilitySpace.integral_comp_eval

Topic: communication   Node: 4052af5ce5b6

Provenance: helper lemma. TCSlib, `CommunicationComplexity.FiniteProbabilitySpace.integral_comp_eval`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/FiniteProbabilitySpace.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Marginal of a coordinate integral over a product space. Let $\iota$ be a finite index type and let $\Omega$ be a finite probability space, so
that the product $\Omega^{\iota}$ of copies of $\Omega$ indexed by $\iota$ carries the
corresponding product probability measure. Fix an index $i \in \iota$ and a function $f
: \Omega \to \bbr$. Then integrating the map $\omega_{\bullet} \mapsto f(\omega_i)$
against the product measure on $\Omega^{\iota}$ gives the same value as integrating $f$
against the measure on $\Omega$:
\[
\int_{\Omega^{\iota}} f(\omega_i) \, d\omega_{\bullet} \;=\; \int_{\Omega} f(\omega)\,
d\omega.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open scoped ProbabilityTheory in
/-- Integrating a function over a coordinate of a finite product space is the same as integrating it over the original finite probability space. -/
theorem CommunicationComplexity.FiniteProbabilitySpace.integral_comp_eval
    {ι Ω : Type*} [Fintype ι] [FiniteProbabilitySpace Ω]
    (i : ι) (f : Ω → ℝ) :
    ∫ ωs : (j : ι) → Ω, f (ωs i) = ∫ ω, f ω := by
  let ν : Measure ((j : ι) → Ω) := Measure.pi fun _ : ι => (volume : Measure Ω)
  have hmap := measurePreserving_eval (μ := fun (_ : ι) => (volume : Measure Ω)) i
  have h1 :
      ∫ ωs : (j : ι) → Ω, f (ωs i) ∂ν =
        ∫ ω, f ω ∂(Measure.map (Function.eval i) ν) :=
    (integral_map (measurable_pi_apply i).aemeasurable
      Measurable.of_discrete.aestronglyMeasurable).symm
  simpa [ν, hmap.map_eq, MeasureTheory.volume_pi] using h1
