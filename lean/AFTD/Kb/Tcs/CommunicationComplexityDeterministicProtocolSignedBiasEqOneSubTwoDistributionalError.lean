import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityBoolSignXor
import AFTD.Kb.Tcs.CommunicationComplexityBoolSignMulBoolSignEqSubTwoIndicator
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolDistributionalError
import AFTD.Kb.Tcs.CommunicationComplexityFiniteProbabilitySpaceMeasureRealEqIntegralIndicatorOne
import AFTD.Kb.Tcs.CommunicationComplexityBoolSign
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityFiniteProbabilitySpace
import AFTD.Kb.Tcs.CommunicationComplexityFiniteMeasureSpace

/-!
# CommunicationComplexity.Deterministic.Protocol.signedBias_eq_one_sub_two_distributionalError

Topic: communication   Node: 4778534b1ed2

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.Protocol.signedBias_eq_one_sub_two_distributionalError`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Discrepancy.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Signed correlation and distributional error. Let $X$ and $Y$ be the input types of Alice and Bob, and let $\mu$ be a finite
probability measure on $X \times Y$. Write $\sigma \colon \mathrm{Bool} \to \{\pm 1\}$
for the map sending $\mathrm{false}$ to $1$ and $\mathrm{true}$ to $-1$. For a
deterministic communication protocol $p$ with Boolean output and a target function $g
\colon X \to Y \to \mathrm{Bool}$, the expected signed correlation between the
protocol's output and the target satisfies
\[
  \E_{(x,y)\sim\mu}\bigl[\sigma\bigl(p(x,y)\bigr)\,\sigma\bigl(g(x,y)\bigr)\bigr]
  \;=\; 1 - 2\,\varepsilon_\mu(p,g),
\]
where $p(x,y)$ denotes the value computed by running $p$ on $(x,y)$ and
$\varepsilon_\mu(p,g) = \mu\bigl(\{(x,y) \mid p(x,y) \ne g(x,y)\}\bigr)$ is the
distributional error of $p$ against $g$ under $\mu$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open scoped BigOperators in
variable {X Y : Type*} in
/-- The expected product of the `±1` signs of the protocol's output and of `g` (the signed bias, or correlation, of `p` with `g` under `μ`) equals `1 − 2e`, where `e` is the distributional error of `p` with respect to `g`: pointwise the product is `1 − 2·1[p errs]`, and the integral of the error indicator is `e`. **Proof sketch.** Let `E` be the set of inputs on which `p` and `g` disagree. (1) Pointwise, the product of the two signs equals `1 − 2·1_E` (`boolSign_mul_boolSign_eq_sub_two_indicator`). (2) Integrate: on a finite space both terms are integrable, the constant `1` integrates to `1` under a probability measure, and the integral of the indicator of `E` is the measure of `E`, which is by definition the distributional error. -/
lemma CommunicationComplexity.Deterministic.Protocol.signedBias_eq_one_sub_two_distributionalError
    [μ : FiniteProbabilitySpace (X × Y)]
    (p : Protocol X Y Bool)
    (g : X → Y → Bool) :
    ∫ xy : X × Y, boolSign (p.run xy.1 xy.2) * boolSign (g xy.1 xy.2) =
      1 - 2 * p.distributionalError μ g := by
  classical
  let Err : Set (X × Y) := {xy : X × Y | p.run xy.1 xy.2 ≠ g xy.1 xy.2}
  have hpoint :
      (fun xy : X × Y => boolSign (p.run xy.1 xy.2) * boolSign (g xy.1 xy.2)) =
      fun xy : X × Y => (1 : ℝ) - 2 * Set.indicator Err 1 xy := by
    ext xy
    by_cases hxy : p.run xy.1 xy.2 ≠ g xy.1 xy.2
    · simp [Err, hxy, boolSign_mul_boolSign_eq_sub_two_indicator]
    · simp [Err, hxy, boolSign_mul_boolSign_eq_sub_two_indicator]
  rw [hpoint]
  rw [integral_sub (Integrable.of_finite) (Integrable.of_finite)]
  rw [MeasureTheory.integral_const]
  rw [MeasureTheory.integral_const_mul]
  rw [← FiniteProbabilitySpace.measureReal_eq_integral_indicator_one
    (Ω := X × Y) Err]
  rw [probReal_univ]
  simp [Deterministic.Protocol.distributionalError, Measure.real, Err]
