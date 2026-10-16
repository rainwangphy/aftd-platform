import AFTD.Prelude
import AFTD.Kb.Tcs.BoolBLREpsilonFarFromLinear
import AFTD.Kb.Tcs.BoolBLRFourierCoeffLeOfFarFromLinear
import AFTD.Kb.Tcs.BoolBLRLiftPm1
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
# BoolBLR.BLR_soundness_via_fourier_aux_h_bound

Topic: interactive   Node: c45747e3fd04

Provenance: helper lemma. TCSlib, `BoolBLR.BLR_soundness_via_fourier_aux_h_bound`. Lean proof by Prastik Mohanraj, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/BLR/BoolBLR.lean (Copyright (c) 2026 Prastik Mohanraj. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Per-coefficient cube bound for functions far from linear. Let $f : \{0,1\}^n \to \{0,1\}$ be $\varepsilon$-far from linear, meaning that $0 \le
\varepsilon \le 1$ and every linear function $g : \{0,1\}^n \to \{0,1\}$ (one satisfying
$g(x \oplus y) = g(x) \oplus g(y)$ for all $x,y$) has distance $\Pr_{x}[f(x) \ne g(x)]
\ge \varepsilon$ from $f$. Write $\hat F(S) = \E[F \cdot \chi_S]$ for the Fourier
coefficient of $F = (-1)^{f}$, the $\pm 1$ lift of $f$, at a subset $S \subseteq [n]$.
Then for every such $S$,
\[
  \hat F(S)^3 \;\le\; \hat F(S)^2\,(1 - 2\varepsilon).
\]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BoolFourier in
lemma BoolBLR.BLR_soundness_via_fourier_aux_h_bound {n : ℕ} (f : BoolFourier.hypercube n → Bool) (ε : ℝ) (hfar : epsilon_far_from_linear f ε) :
    ∀ (S : Finset (Fin n)),
  BoolFourier.fourier_coeff (lift_pm1 f) S ^ 3 ≤ BoolFourier.fourier_coeff (lift_pm1 f) S ^ 2 * (1 - 2 * ε) :=
  by
  exact fun S => by nlinarith only [ show fourier_coeff ( lift_pm1 f ) S ≤ 1 - 2 * ε by exact fourier_coeff_le_of_far_from_linear f ε hfar S ] ;
