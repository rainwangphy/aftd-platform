import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityRnDensity

/-!
# CommunicationComplexity.rnDensity_nonneg

Topic: information   Node: a7e80c9d8010

Provenance: helper lemma. TCSlib, `CommunicationComplexity.rnDensity_nonneg`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Nonnegativity of the Radon–Nikodym density. Let $\mu$ and $\nu$ be probability measures on a measurable space $\Omega$. Then at
every point $x \in \Omega$, the real-valued Radon–Nikodym density $\frac{d\mu}{d\nu}(x)$
satisfies $\frac{d\mu}{d\nu}(x) \ge 0$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open ProbabilityTheory in
open scoped ENNReal in
/-- The density `dμ/dν` is pointwise nonnegative. -/
theorem CommunicationComplexity.rnDensity_nonneg
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (x : Ω) :
    0 ≤ rnDensity μ ν x :=
  ENNReal.toReal_nonneg
