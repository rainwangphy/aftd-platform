import AFTD.Prelude
import AFTD.Kb.Tcs.BoolBLRLiftPm1
import AFTD.Kb.Tcs.BoolFourierBoolToPM1Sq
import AFTD.Kb.Tcs.BoolFourierL2NormSq
import AFTD.Kb.Tcs.BoolFourierExpectation
import AFTD.Kb.Tcs.BoolFourierFourierCoeff
import AFTD.Kb.Tcs.BoolFourierHypercube
import AFTD.Kb.Tcs.BoolFourierParsevalIdentity

/-!
# BoolBLR.BLR_soundness_via_fourier_aux_hparseval

Topic: interactive   Node: ad2c4af1846b

Provenance: helper lemma. TCSlib, `BoolBLR.BLR_soundness_via_fourier_aux_hparseval`. Lean proof by Prastik Mohanraj, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/BLR/BoolBLR.lean (Copyright (c) 2026 Prastik Mohanraj. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Parseval identity for the sign lift of a Boolean function. Let $f : \{0,1\}^n \to \{0,1\}$ be a Boolean-valued function, and let $g : \{0,1\}^n \to
\bbr$ be its $\pm 1$ lift, given by $g(x) = (-1)^{f(x)}$. Then the Fourier coefficients
$\hat g(S) = \langle g, \chi_S\rangle$, taken over all subsets $S \subseteq [n]$,
satisfy
\[
  \sum_{S \subseteq [n]} \hat g(S)^2 \;=\; 1.
\]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BoolFourier in
lemma BoolBLR.BLR_soundness_via_fourier_aux_hparseval {n : ℕ} (f : BoolFourier.hypercube n → Bool) :
    ∑ S, BoolFourier.fourier_coeff (lift_pm1 f) S ^ 2 = 1 :=
  by
  convert parseval_identity ( lift_pm1 f ) using 1;
  unfold L2_norm_sq lift_pm1;
  unfold expectation; norm_num [ BoolToPM1_sq ] ;
