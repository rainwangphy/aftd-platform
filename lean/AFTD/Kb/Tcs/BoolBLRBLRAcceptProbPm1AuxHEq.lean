import AFTD.Prelude
import AFTD.Kb.Tcs.BoolBLRLiftPm1
import AFTD.Kb.Tcs.BoolFourierHypercube
import AFTD.Kb.Tcs.BoolFourierXorVec
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSign
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignFalse
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignTrue
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignSq
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignMulSelf
import AFTD.Kb.Tcs.BooleanAnalysisChiSSingleton
import AFTD.Kb.Tcs.BooleanAnalysisSumBoolToSign
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignNot

/-!
# BoolBLR.BLR_accept_prob_pm1_aux_h_eq

Topic: interactive   Node: 29df25d871f8

Provenance: helper lemma. TCSlib, `BoolBLR.BLR_accept_prob_pm1_aux_h_eq`. Lean proof by Prastik Mohanraj, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/BLR/BoolBLR.lean (Copyright (c) 2026 Prastik Mohanraj. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Pointwise $\pm 1$ form of the BLR indicator. Fix $n \in \bbn$ and a Boolean-valued function $f : \{0,1\}^n \to \{0,1\}$, and let $g :
\{0,1\}^n \to \bbr$ be its $\pm 1$ lift, $g(x) = (-1)^{f(x)}$. Then for all $x, y \in
\{0,1\}^n$,
\[
  \mathbf{1}\!\left[\, g(x \oplus y) = g(x)\,g(y) \,\right]
  \;=\;
  \frac{1 + g(x)\,g(y)\,g(x \oplus y)}{2},
\]
where $x \oplus y$ denotes the componentwise XOR and the left-hand side is $1$ when the
equality holds and $0$ otherwise.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BoolFourier in
lemma BoolBLR.BLR_accept_prob_pm1_aux_h_eq {n : ℕ} (f : BoolFourier.hypercube n → Bool) :
    ∀ (x y : BoolFourier.hypercube n),
  (if lift_pm1 f (BoolFourier.xor_vec x y) = lift_pm1 f x * lift_pm1 f y then 1 else 0) =
    (1 + lift_pm1 f x * lift_pm1 f y * lift_pm1 f (BoolFourier.xor_vec x y)) / 2 :=
  by
  intro x y; split_ifs;
  -- Accept case: triple product is +1, so (1+1)/2 = 1.
  · cases h : f x <;> cases h' : f y <;> simp_all +decide [ lift_pm1 ] <;> norm_num [BooleanAnalysis.boolToSign] at *;
  -- Reject case: triple product is -1, so (1-1)/2 = 0.
  · cases h : f x <;> cases h' : f y <;> cases h'' : f ( xor_vec x y ) <;> simp_all +decide [ lift_pm1 ] <;> norm_num [BooleanAnalysis.boolToSign] at *;
