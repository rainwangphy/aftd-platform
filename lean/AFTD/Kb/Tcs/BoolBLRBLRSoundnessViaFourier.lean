import AFTD.Prelude
import AFTD.Kb.Tcs.BoolBLREpsilonFarFromLinear
import AFTD.Kb.Tcs.BoolBLRLiftPm1
import AFTD.Kb.Tcs.BoolBLRBLRSoundnessViaFourierAuxHBound
import AFTD.Kb.Tcs.BoolBLRBLRSoundnessViaFourierAuxHparseval
import AFTD.Kb.Tcs.BoolFourierFourierCoeff
import AFTD.Kb.Tcs.BoolFourierHypercube
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignFalse
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignTrue
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignSq
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignMulSelf
import AFTD.Kb.Tcs.BooleanAnalysisChiSSingleton
import AFTD.Kb.Tcs.BooleanAnalysisSumBoolToSign
import AFTD.Kb.Tcs.BooleanAnalysisInnerProductChiSelf
import AFTD.Kb.Tcs.BooleanAnalysisFlipBitFlipBit
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignNot
import AFTD.Kb.Tcs.BooleanAnalysisInstAddCommGroupBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisInstModuleRealBooleanFunc

/-!
# BoolBLR.BLR_soundness_via_fourier

Topic: interactive   Node: 82bb82f95926

Provenance: helper lemma. TCSlib, `BoolBLR.BLR_soundness_via_fourier`. Lean proof by Prastik Mohanraj, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/BLR/BoolBLR.lean (Copyright (c) 2026 Prastik Mohanraj. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Sum of cubed Fourier coefficients bounds distance to linearity. Let $f : \{0,1\}^n \to \{0,1\}$ be a Boolean function and let $\varepsilon \in \bbr$
with $0 \le \varepsilon \le 1$, and suppose $f$ is $\varepsilon$-far from linear: for
every linear function $g : \{0,1\}^n \to \{0,1\}$ one has $\dist(f,g) \ge \varepsilon$.
Writing $F = (-1)^{f}$ for the $\pm 1$ lift of $f$ and $\hat F(S) = \langle F,
\chi_S\rangle$ for its Fourier coefficient at $S \subseteq [n]$, the sum of the cubed
coefficients over all subsets satisfies
\[
  \sum_{S \subseteq [n]} \hat F(S)^3 \;\le\; 1 - 2\varepsilon.
\]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BoolFourier in
/-- Proves the Fourier-analytic upper bound on BLR acceptance for far functions. **Source:** [OD14, §1.6]. -/
lemma BoolBLR.BLR_soundness_via_fourier {n : ℕ}
    (f : hypercube n → Bool)
    (ε : ℝ)
    (hfar : epsilon_far_from_linear f ε) :
  ∑ S : Finset (Fin n), (fourier_coeff (lift_pm1 f) S) ^ 3
    ≤ 1 - 2 * ε := by
    -- Parseval for ±1-valued lift_pm1: each (lift_pm1 f)(x)^2 = 1, so ‖f‖_2^2 = 1.
    -- f̂(S)^3 = f̂(S)^2 · f̂(S) ≤ f̂(S)^2 · (1 - 2ε), since f̂(S)^2 ≥ 0 and f̂(S) ≤ 1 - 2ε.
    -- Sum the per-S bound and apply Parseval.
    convert Finset.sum_le_sum fun S _ => (BLR_soundness_via_fourier_aux_h_bound f ε hfar) S using 1 <;> first | rfl | (rw [ ← Finset.sum_mul _ _ _ ] ; simp_all only [one_mul, (BLR_soundness_via_fourier_aux_hparseval f)])
