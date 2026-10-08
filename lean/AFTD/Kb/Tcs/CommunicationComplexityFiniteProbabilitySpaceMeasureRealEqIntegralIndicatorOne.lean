import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityFiniteProbabilitySpace

/-!
# CommunicationComplexity.FiniteProbabilitySpace.measureReal_eq_integral_indicator_one

Topic: communication   Node: b11eb580f597

Provenance: helper lemma. TCSlib, `CommunicationComplexity.FiniteProbabilitySpace.measureReal_eq_integral_indicator_one`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/FiniteProbabilitySpace.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Measure of a set as the integral of its indicator. Let $\Omega$ be a finite probability space and let $S \subseteq \Omega$. Then the
(real-valued) probability of $S$ equals the integral over $\Omega$ of the indicator
function of $S$, taken with value $1$ on $S$ and $0$ elsewhere:
\[
\mathbb{P}(S) \;=\; \int_{\Omega} \mathbf{1}_S(\omega)\, d\omega,
\]
where $\mathbf{1}_S \colon \Omega \to \bbr$ is the function equal to $1$ at points of
$S$ and $0$ at points outside $S$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open scoped ProbabilityTheory in
/-- The real-valued measure of a set is the integral of its indicator. -/
theorem CommunicationComplexity.FiniteProbabilitySpace.measureReal_eq_integral_indicator_one
    {Ω : Type*} [FiniteProbabilitySpace Ω] (S : Set Ω) :
    volume.real S = ∫ ω, Set.indicator S (1 : Ω → ℝ) ω := by
  rw [MeasureTheory.integral_indicator_one MeasurableSet.of_discrete]
