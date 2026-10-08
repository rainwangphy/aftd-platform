import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisSumBoolToSign
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignMulSelf
import AFTD.Kb.Tcs.BooleanAnalysisChiSSingleton
import AFTD.Kb.Tcs.BooleanAnalysisInstModuleRealBooleanFunc
import AFTD.Kb.Tcs.BoolFourierBoolToPM1
import AFTD.Kb.Tcs.BoolFourierHypercube
import AFTD.Kb.Tcs.BooleanAnalysisBoolCube
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignTrue
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignFalse
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignNot
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignSq
import AFTD.Kb.Tcs.BoolBLRLiftPm1
import AFTD.Kb.Tcs.BooleanAnalysisInstAddCommGroupBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisFlipBitFlipBit

/-!
# BoolBLR.fourier_coeff_le_of_dist_ge_aux_h_lift_pm1

Topic: interactive   Node: 8bca29647a31

Provenance: helper lemma. TCSlib, `BoolBLR.fourier_coeff_le_of_dist_ge_aux_h_lift_pm1`. Lean proof by Prastik Mohanraj, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/BLR/BoolBLR.lean (Copyright (c) 2026 Prastik Mohanraj. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Product of $\pm 1$ lifts as a disagreement indicator. Let $f, g : \{0,1\}^n \to \{0,1\}$ be Boolean-valued functions on the hypercube, and
write $F, G : \{0,1\}^n \to \bbr$ for their $\pm 1$ lifts, given by $F(x) = (-1)^{f(x)}$
and $G(x) = (-1)^{g(x)}$. Then for every point $x \in \{0,1\}^n$,
\[
  F(x)\,G(x) \;=\; 1 - 2\cdot\mathbf{1}\!\left[f(x) \ne g(x)\right],
\]
so the product equals $+1$ where $f$ and $g$ agree at $x$ and $-1$ where they disagree.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BoolFourier in
lemma BoolBLR.fourier_coeff_le_of_dist_ge_aux_h_lift_pm1 {n : ℕ} (f : BoolFourier.hypercube n → Bool) (g : BoolFourier.hypercube n → Bool) :
    ∀ (x : BooleanAnalysis.BoolCube n), lift_pm1 f x * lift_pm1 g x = 1 - 2 * if f x = g x then 0 else 1 :=
  by
  unfold lift_pm1;
  intro x; rcases f x with ( _ | _ | f ) <;> rcases g x with ( _ | _ | g ) <;> norm_num [ BoolToPM1 ] ;
