import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolLeafRectangles
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolLeafRectanglesCard
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolLeafRectanglesIsRectangle
import AFTD.Kb.Tcs.CommunicationComplexityBoolSign
import AFTD.Kb.Tcs.CommunicationComplexityRectangleIsRectangle
import AFTD.Kb.Tcs.CommunicationComplexityDiscrepancy
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolLeafRectanglesFinset
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolMemLeafRectanglesFinset
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolNonnegOfDiscrepancyBound
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolRectangleSign
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolRectangleSignAbs
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSignedBiasEqOneSubTwoDistributionalError
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolSignedBiasEqSumRectangles
import AFTD.Kb.Tcs.CommunicationComplexityFiniteProbabilitySpace
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolDistributionalError
import AFTD.Kb.Tcs.CommunicationComplexityBoolSignXor
import AFTD.Kb.Tcs.G
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicFiniteMessageProtocolComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicOneWayProtocolRun

/-!
# CommunicationComplexity.Deterministic.Protocol.one_sub_two_distributionalError_le_two_pow_mul

Topic: communication   Node: 6ecd497d8c45

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.Protocol.one_sub_two_distributionalError_le_two_pow_mul`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Discrepancy.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Discrepancy lower bound on distributional error. Let $\mu$ be a finite probability measure on $X \times Y$, let $g : X \times Y \to
\mathrm{Bool}$, and let $\gamma \in \bbr$ be such that every rectangle $R \subseteq X
\times Y$ satisfies $\abs{\mathrm{disc}_\mu(g, R)} \le \gamma$. Then for every
deterministic Boolean-valued communication protocol $p$, writing $\mathrm{err}$ for the
$\mu$-probability that $p$ disagrees with $g$ (that is, the measure of $\{(x,y) : p(x,y)
\ne g(x,y)\}$) and $c$ for the communication complexity of $p$,
\[
  1 - 2\,\mathrm{err} \;\le\; 2^{c}\cdot\gamma .
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open scoped BigOperators in
variable {X Y : Type*} in
/-- Core discrepancy bound: if every combinatorial rectangle has absolute discrepancy at most `γ` (with respect to `μ`), then every deterministic Boolean protocol `p` of complexity `c` and distributional error `e` (with respect to `μ` and `g`) satisfies `1 − 2e ≤ 2^c · γ`. [RY20, Thm 5.2 proof] (`1 − 2e ≤ 2^c · γ`). **Proof sketch.** Step 1: `γ ≥ 0`, and each leaf rectangle `R` of `p` is a rectangle, so `|rectangleSign p R · disc(g, R)| ≤ γ`. Step 2: by the triangle inequality, the sum over the leaf rectangles of these signed discrepancies has absolute value at most `(number of leaf rectangles) · γ`. Step 3: a protocol of complexity `c` has at most `2^c` leaf rectangles. Step 4: the signed bias of `p` with `g` equals that sum (`signedBias_eq_sum_rectangles`), hence is bounded by `2^c · γ` in absolute value. Step 5: the signed bias equals `1 − 2e` (`signedBias_eq_one_sub_two_distributionalError`), and `1 − 2e ≤ |1 − 2e|`. -/
theorem CommunicationComplexity.Deterministic.Protocol.one_sub_two_distributionalError_le_two_pow_mul
    [μ : FiniteProbabilitySpace (X × Y)]
    (g : X → Y → Bool) (γ : ℝ)
    (p : Protocol X Y Bool)
    (hdisc : ∀ R : Set (X × Y), Rectangle.IsRectangle R → |discrepancy g R| ≤ γ) :
    1 - 2 * p.distributionalError μ g ≤ (2 : ℝ) ^ p.complexity * γ := by
  -- Step 1: γ ≥ 0 and each leaf rectangle's signed discrepancy is at most γ
  have hγ_nonneg := nonneg_of_discrepancy_bound (μ := μ) g γ hdisc
  have hrect :
      ∀ R ∈ leafRectanglesFinset p, |rectangleSign p R * discrepancy g R| ≤ γ := by
    intro R hR
    have hRrect :
        Rectangle.IsRectangle R :=
      Deterministic.Protocol.leafRectangles_isRectangle p R
        ((mem_leafRectanglesFinset p R).1 hR)
    calc
      |rectangleSign p R * discrepancy g R|
          = |rectangleSign p R| * |discrepancy g R| := by rw [abs_mul]
      _ = |discrepancy g R| := by rw [rectangleSign_abs, one_mul]
      _ ≤ γ := hdisc R hRrect
  -- Step 2: triangle inequality over the leaf rectangles
  have hsum :
      |Finset.sum (leafRectanglesFinset p) (fun R => rectangleSign p R * discrepancy g R)|
        ≤ ((leafRectanglesFinset p).card : ℝ) * γ := by
    calc
      |Finset.sum (leafRectanglesFinset p) (fun R => rectangleSign p R * discrepancy g R)|
          ≤ Finset.sum (leafRectanglesFinset p)
              (fun R => |rectangleSign p R * discrepancy g R|) := by
            simpa using
              (Finset.abs_sum_le_sum_abs (s := leafRectanglesFinset p)
                (f := fun R => rectangleSign p R * discrepancy g R))
      _ ≤ Finset.sum (leafRectanglesFinset p) (fun _ => γ) := by
            exact Finset.sum_le_sum (fun R hR => hrect R hR)
      _ = ((leafRectanglesFinset p).card : ℝ) * γ := by
            simp [nsmul_eq_mul]
  -- Step 3: at most 2^c leaf rectangles
  have hcard :
      ((leafRectanglesFinset p).card : ℝ) ≤ (2 : ℝ) ^ p.complexity := by
    have hcard_nat : (leafRectanglesFinset p).card ≤ 2 ^ p.complexity := by
      rw [show (leafRectanglesFinset p).card = p.leafRectangles.ncard by
        simpa [leafRectanglesFinset] using
          (Set.ncard_eq_toFinset_card p.leafRectangles (Set.toFinite p.leafRectangles)).symm]
      simpa using (Deterministic.Protocol.leafRectangles_card p)
    exact_mod_cast hcard_nat
  -- Step 4: the signed bias is the rectangle sum, hence bounded by 2^c · γ
  have hbias :
      |∫ xy : X × Y, boolSign (p.run xy.1 xy.2) * boolSign (g xy.1 xy.2)|
        ≤ (2 : ℝ) ^ p.complexity * γ := by
    rw [signedBias_eq_sum_rectangles]
    exact hsum.trans (mul_le_mul_of_nonneg_right hcard hγ_nonneg)
  -- Step 5: the signed bias is 1 − 2e
  have habs :
      |1 - 2 * p.distributionalError μ g| ≤ (2 : ℝ) ^ p.complexity * γ := by
    simpa [signedBias_eq_one_sub_two_distributionalError] using hbias
  exact (le_abs_self _).trans habs
