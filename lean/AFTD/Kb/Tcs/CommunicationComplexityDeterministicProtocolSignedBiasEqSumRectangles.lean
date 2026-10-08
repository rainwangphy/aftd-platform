import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolRectangleSign
import AFTD.Kb.Tcs.CommunicationComplexityBoolSignXor
import AFTD.Kb.Tcs.CommunicationComplexityDiscrepancy
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSumIndicatorLeafRectanglesEq
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolLeafRectanglesFinset
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityBoolSign
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityFiniteProbabilitySpace
import AFTD.Kb.Tcs.CommunicationComplexityFiniteMeasureSpace

/-!
# CommunicationComplexity.Deterministic.Protocol.signedBias_eq_sum_rectangles

Topic: communication   Node: 1f67dba7a320

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.Protocol.signedBias_eq_sum_rectangles`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Discrepancy.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Signed bias as a sum over leaf rectangles. Let $\mu$ be a finite probability space on $X \times Y$, let $p$ be a deterministic
Boolean communication protocol with input types $X$ and $Y$, and let $g : X \to Y \to
\mathrm{Bool}$. Writing $\sigma$ for the sign map sending $\mathrm{false}$ to $1$ and
$\mathrm{true}$ to $-1$, the signed bias of $p$ against $g$ satisfies
\[
  \E_{(x,y)\sim\mu}\bigl[\sigma\bigl(p(x,y)\bigr)\cdot\sigma\bigl(g(x,y)\bigr)\bigr]
  \;=\;
  \sum_{R}\; s(p,R)\,\cdot\,\mathrm{disc}_\mu(g,R),
\]
where the sum runs over the (finitely many) leaf rectangles $R$ of $p$, the value
$p(x,y)$ is the output of $p$ on inputs $x$ and $y$, the rectangle sign $s(p,R)$ equals
$+1$ if $p$ outputs $\mathrm{false}$ at every point of $R$ and $-1$ otherwise, and
$\mathrm{disc}_\mu(g,R) = \E_{(x,y)\sim\mu}[\mathbf{1}_R(x,y)\cdot\sigma(g(x,y))]$ is
the discrepancy of $g$ on $R$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open scoped BigOperators in
variable {X Y : Type*} in
/-- The signed bias of `p` with `g` equals the sum, over the leaf rectangles `R` of `p`, of the rectangle sign of `R` times the discrepancy of `g` on `R`. **Proof sketch.** Pointwise, replace the sign of the protocol's output by the sum of signed rectangle indicators (`sum_indicator_leafRectangles_eq`) and distribute the sign of `g` over the sum. Then exchange the finite sum with the integral and identify each term with `rectangleSign p R` times the integral defining `discrepancy g R`. -/
lemma CommunicationComplexity.Deterministic.Protocol.signedBias_eq_sum_rectangles
    [μ : FiniteProbabilitySpace (X × Y)]
    (p : Protocol X Y Bool)
    (g : X → Y → Bool) :
    ∫ xy : X × Y, boolSign (p.run xy.1 xy.2) * boolSign (g xy.1 xy.2) =
      Finset.sum (leafRectanglesFinset p) (fun R => rectangleSign p R * discrepancy g R) := by
  classical
  have hpoint :
      (fun xy : X × Y => boolSign (p.run xy.1 xy.2) * boolSign (g xy.1 xy.2)) =
      fun xy : X × Y =>
        Finset.sum (leafRectanglesFinset p)
          (fun R => Set.indicator R (fun _ => rectangleSign p R) xy * boolSign (g xy.1 xy.2)) := by
    ext xy
    calc
      boolSign (p.run xy.1 xy.2) * boolSign (g xy.1 xy.2) =
          (Finset.sum (leafRectanglesFinset p)
            (fun R => Set.indicator R (fun _ => rectangleSign p R) xy)) *
            boolSign (g xy.1 xy.2) := by
              rw [sum_indicator_leafRectangles_eq p xy]
      _ = Finset.sum (leafRectanglesFinset p)
            (fun R => Set.indicator R (fun _ => rectangleSign p R) xy *
              boolSign (g xy.1 xy.2)) := by
              rw [Finset.sum_mul]
  rw [hpoint, MeasureTheory.integral_finset_sum]
  · refine Finset.sum_congr rfl ?_
    intro R hR
    have hterm :
        (fun xy : X × Y =>
          Set.indicator R (fun _ => rectangleSign p R) xy * boolSign (g xy.1 xy.2)) =
        fun xy : X × Y =>
          rectangleSign p R * ((if xy ∈ R then (1 : ℝ) else 0) * boolSign (g xy.1 xy.2)) := by
      ext xy
      by_cases hxy : xy ∈ R <;> simp [hxy, mul_comm]
    rw [hterm, MeasureTheory.integral_const_mul, discrepancy]
  · intro R hR
    exact Integrable.of_finite
