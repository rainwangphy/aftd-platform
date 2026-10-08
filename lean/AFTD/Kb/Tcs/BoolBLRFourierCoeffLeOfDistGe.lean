import AFTD.Prelude
import AFTD.Kb.Tcs.BoolBLRBoolDist
import AFTD.Kb.Tcs.BoolBLRLiftPm1
import AFTD.Kb.Tcs.BoolBLRFourierCoeffLeOfDistGeAuxHLiftPm1
import AFTD.Kb.Tcs.BoolFourierCardHypercube
import AFTD.Kb.Tcs.BoolFourierCharS
import AFTD.Kb.Tcs.BoolFourierExpectation
import AFTD.Kb.Tcs.BoolFourierFourierCoeff
import AFTD.Kb.Tcs.BoolFourierHypercube
import AFTD.Kb.Tcs.BoolFourierInnerProduct
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
import AFTD.Kb.Tcs.G

/-!
# BoolBLR.fourier_coeff_le_of_dist_ge

Topic: interactive   Node: 8c7a3707948a

Provenance: helper lemma. TCSlib, `BoolBLR.fourier_coeff_le_of_dist_ge`. Lean proof by Prastik Mohanraj, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/BLR/BoolBLR.lean (Copyright (c) 2026 Prastik Mohanraj. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Fourier coefficient bound from distance. Let $f,g:\{0,1\}^n\to\{0,1\}$ be Boolean-valued functions, let $S\subseteq[n]$, and let
$\varepsilon\in\bbr$. Write $f^{\pm},g^{\pm}:\{0,1\}^n\to\bbr$ for their $\pm1$ lifts,
given by $x\mapsto(-1)^{f(x)}$ and $x\mapsto(-1)^{g(x)}$. Suppose that $g^{\pm}$
coincides with the Walsh character $\chi_S$, and that $\dist(f,g)=\Pr_{x}[f(x)\ne
g(x)]\ge\varepsilon$. Then the Fourier coefficient of $f^{\pm}$ at $S$ satisfies
\[\widehat{f^{\pm}}(S)\;\le\;1-2\varepsilon.\]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BoolFourier in
/-- Bounds a Fourier coefficient using distance from the corresponding linear function. **Source:** [OD14, §1.6 (Fourier soundness proof)]. -/
lemma BoolBLR.fourier_coeff_le_of_dist_ge
    {n : ℕ}
    (f g : hypercube n → Bool)
    (S : Finset (Fin n))
    (hchar : lift_pm1 g = char_S S)
    (hdist : bool_dist f g ≥ ε) :
    fourier_coeff (lift_pm1 f) S ≤ 1 - 2 * ε := by
  -- Reduce to f̂(S) ≤ 1 - 2 · dist(f,g).
  refine le_trans ?_ ( sub_le_sub_left ( mul_le_mul_of_nonneg_left hdist <| by norm_num ) 1 );
  unfold fourier_coeff bool_dist;
  unfold inner_product expectation;
  -- Pointwise identity: lift(f)(x)·lift(g)(x) = 1 - 2·𝟙[f(x) ≠ g(x)].
  simp_all +decide [ ← hchar, Finset.sum_ite , (fourier_coeff_le_of_dist_ge_aux_h_lift_pm1 f g)];
  ring_nf; norm_num [ card_hypercube ] ;
  norm_num [ ← mul_pow ]

-- if f is epsilon-far from all linear functions, then f-hat (S) ≤ 1 - 2 * ε for all S
