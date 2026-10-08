import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityIntegrableRnDensity
import AFTD.Kb.Tcs.CommunicationComplexityRnDensity

/-!
# CommunicationComplexity.integrable_rnDensity_sub_one

Topic: information   Node: 3b14468e431f

Provenance: helper lemma. TCSlib, `CommunicationComplexity.integrable_rnDensity_sub_one`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Integrability of the Radon–Nikodym density minus one. Let $\mu$ and $\nu$ be probability measures on a measurable space $\Omega$, and let
$\frac{d\mu}{d\nu}\colon \Omega \to \bbr$ denote the real-valued Radon–Nikodym density
of $\mu$ with respect to $\nu$. Then the function $x \mapsto \frac{d\mu}{d\nu}(x) - 1$
is integrable with respect to $\nu$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open ProbabilityTheory in
open scoped ENNReal in
/-- The centred density `dμ/dν − 1` is `ν`-integrable. -/
theorem CommunicationComplexity.integrable_rnDensity_sub_one
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    Integrable (fun x => rnDensity μ ν x - 1) ν :=
  (integrable_rnDensity μ ν).sub (integrable_const 1)
