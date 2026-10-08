import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDiscrepancy
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolOneSubTwoDistributionalErrorLeTwoPowMul
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolDistributionalError
import AFTD.Kb.Tcs.CommunicationComplexityRectangleIsRectangle
import AFTD.Kb.Tcs.CommunicationComplexityFiniteProbabilitySpace

/-!
# CommunicationComplexity.Deterministic.Protocol.logb_le_complexity_of_distributionalError

Topic: communication   Node: 5da720f19622

Provenance: formalization of a published result. Source: Discrepancy lower bound on communication complexity, as formalized in TCSlib (`CommunicationComplexity.Deterministic.Protocol.logb_le_complexity_of_distributionalError`). Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Discrepancy.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Discrepancy lower bound on communication complexity. Let $\mu$ be a finite probability space on $X \times Y$, let $g : X \times Y \to
\mathrm{Bool}$ be a Boolean function, and let $\gamma > 0$ be a real number such that
every combinatorial rectangle $R \subseteq X \times Y$ satisfies
$\abs{\mathrm{disc}_\mu(g, R)} \le \gamma$, where $\mathrm{disc}_\mu(g, R) =
\E_{(x,y)\sim\mu}[\mathbf{1}_R(x,y)\,\sigma(g(x,y))]$ and $\sigma(\mathrm{false}) = 1$,
$\sigma(\mathrm{true}) = -1$. Let $p$ be a deterministic communication protocol with
Boolean outputs, and let $\varepsilon = \mu(\{(x,y) : p(x,y) \ne g(x,y)\})$ be its
distributional error in computing $g$ under $\mu$. If $1 - 2\varepsilon > 0$, then the
communication complexity of $p$ satisfies
\[
  \log_2\!\left(\frac{1 - 2\varepsilon}{\gamma}\right) \;\le\; \mathrm{complexity}(p).
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open scoped BigOperators in
variable {X Y : Type*} in
/-- Discrepancy bound in logarithmic form: if every rectangle has absolute discrepancy at most `γ > 0` and a deterministic Boolean protocol `p` has distributional error `e` with `1 − 2e > 0`, then `log₂((1 − 2e) / γ) ≤ complexity of p`. [RY20, Thm 5.2] (distributional form: `log₂((1−2e)/γ) ≤ c`). Follows from `one_sub_two_distributionalError_le_two_pow_mul` by dividing by `γ` and taking logarithms. -/
theorem CommunicationComplexity.Deterministic.Protocol.logb_le_complexity_of_distributionalError
    [μ : FiniteProbabilitySpace (X × Y)]
    (g : X → Y → Bool) (γ : ℝ)
    (p : Protocol X Y Bool)
    (hdisc : ∀ R : Set (X × Y), Rectangle.IsRectangle R → |discrepancy g R| ≤ γ)
    (hγ : 0 < γ)
    (herr : 0 < 1 - 2 * p.distributionalError μ g) :
    Real.logb 2 ((1 - 2 * p.distributionalError μ g) / γ) ≤ p.complexity := by
  have hmain := one_sub_two_distributionalError_le_two_pow_mul (μ := μ) g γ p hdisc
  have hdiv :
      (1 - 2 * p.distributionalError μ g) / γ ≤ (2 : ℝ) ^ p.complexity := by
    rw [div_le_iff₀ hγ]
    exact hmain
  have hpos : 0 < (1 - 2 * p.distributionalError μ g) / γ := by
    positivity
  rw [Real.logb_le_iff_le_rpow (b := (2 : ℝ)) (hb := by norm_num) hpos]
  simpa [Real.rpow_natCast] using hdiv
