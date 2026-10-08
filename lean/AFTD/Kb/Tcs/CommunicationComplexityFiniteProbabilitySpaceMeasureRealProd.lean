import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityFiniteProbabilitySpace

/-!
# CommunicationComplexity.FiniteProbabilitySpace.measureReal_prod

Topic: communication   Node: 22ede8954cd4

Provenance: helper lemma. TCSlib, `CommunicationComplexity.FiniteProbabilitySpace.measureReal_prod`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/FiniteProbabilitySpace.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Product measure of a rectangle. Let $\Omega_1$ and $\Omega_2$ be finite probability spaces, with respective probability
measures $\bbP_1$ and $\bbP_2$, and let $A \subseteq \Omega_1$ and $B \subseteq
\Omega_2$ be any subsets. Then, under the product probability measure $\bbP$ on
$\Omega_1 \times \Omega_2$, the measure of the rectangle $A \times B$ factors as
\[
  \bbP(A \times B) \;=\; \bbP_1(A) \cdot \bbP_2(B),
\]
where each quantity is taken as a real number.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open scoped ProbabilityTheory in
/-- The real-valued measure of a measurable rectangle in a product finite probability space factors as the product of the two measures. -/
theorem CommunicationComplexity.FiniteProbabilitySpace.measureReal_prod
    {Ω₁ Ω₂ : Type*} [FiniteProbabilitySpace Ω₁] [FiniteProbabilitySpace Ω₂]
    (A : Set Ω₁) (B : Set Ω₂) :
    volume.real (A ×ˢ B : Set (Ω₁ × Ω₂)) =
      volume.real A * volume.real B := by
  rw [Measure.real, Measure.real, Measure.real]
  rw [show (volume : Measure (Ω₁ × Ω₂)) = volume.prod volume from rfl]
  rw [Measure.prod_prod, ENNReal.toReal_mul]
