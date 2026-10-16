import AFTD.Prelude
import AFTD.Kb.Tcs.BoolBLRBLRAcceptProb
import AFTD.Kb.Tcs.BoolBLRBLRAcceptProbPm1
import AFTD.Kb.Tcs.BoolBLRBLRSoundnessViaFourier
import AFTD.Kb.Tcs.BoolBLREpsilonFarFromLinear
import AFTD.Kb.Tcs.BoolBLRTripleExpectationEqCubeFourier
import AFTD.Kb.Tcs.BoolFourierHypercube
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignFalse
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignTrue
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignSq
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignMulSelf
import AFTD.Kb.Tcs.BooleanAnalysisChiSSingleton
import AFTD.Kb.Tcs.BooleanAnalysisSumBoolToSign
import AFTD.Kb.Tcs.BooleanAnalysisFlipBitFlipBit
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignNot
import AFTD.Kb.Tcs.BooleanAnalysisInstAddCommGroupBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisInstModuleRealBooleanFunc
import AFTD.Kb.Tcs.BoolFourierXorVec
import AFTD.Kb.Tcs.BoolBLRLiftPm1
import AFTD.Kb.Tcs.BoolFourierFourierCoeff
import AFTD.Kb.Tcs.BoolFourierExpectation
import AFTD.Kb.Tcs.BooleanAnalysisBoolCube

/-!
# BoolBLR.BLR_soundness

Topic: interactive   Node: b046ae055605

Provenance: formalization of a published result. Source: Soundness of the BLR linearity test, as formalized in TCSlib (`BoolBLR.BLR_soundness`). Lean proof by Prastik Mohanraj, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/BLR/BoolBLR.lean (Copyright (c) 2026 Prastik Mohanraj. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Soundness of the BLR linearity test. Let $f : \{0,1\}^n \to \{0,1\}$ and let $\varepsilon \in \bbr$ satisfy $0 \le
\varepsilon \le 1$. Suppose $f$ is $\varepsilon$-far from linear, meaning that every
linear function $g : \{0,1\}^n \to \{0,1\}$ (one satisfying $g(x \oplus y) = g(x) \oplus
g(y)$ for all $x, y$) has distance $\Pr_{x}[f(x) \ne g(x)] \ge \varepsilon$ from $f$.
Then the BLR acceptance probability of $f$ satisfies
\[
\E_{x}\!\left[\E_{y}\!\left[\mathbf{1}\!\left[(-1)^{f(x \oplus y)} =
(-1)^{f(x)}\,(-1)^{f(y)}\right]\right]\right] \;\le\; 1 - \varepsilon,
\]
where $x$ and $y$ range uniformly over $\{0,1\}^n$; equivalently, the test rejects $f$
with probability at least $\varepsilon$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BoolFourier in
/-- Shows that a function `ε`-far from linearity is rejected by BLR with probability at least `ε`. **Source:** [OD14, §1.6]. -/
lemma BoolBLR.BLR_soundness {n : ℕ}
    (f : hypercube n → Bool)
    (ε : ℝ)
    (hfar : epsilon_far_from_linear f ε) :
  BLR_accept_prob f ≤ 1 - ε := by
  rw [BLR_accept_prob_pm1];
  -- Combine the cube-sum identity and the soundness bound; linarith finishes.
  linarith [ BLR_soundness_via_fourier f ε hfar, triple_expectation_eq_cube_fourier f ]
