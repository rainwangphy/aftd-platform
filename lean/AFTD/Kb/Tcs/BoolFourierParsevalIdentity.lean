import AFTD.Prelude
import AFTD.Kb.Tcs.BoolFourierBoolFun
import AFTD.Kb.Tcs.BoolFourierL2NormSq
import AFTD.Kb.Tcs.BoolFourierFourierCoeff
import AFTD.Kb.Tcs.BoolFourierFourierCoeffEq
import AFTD.Kb.Tcs.BoolFourierParsevalIdentityAuxHL2
import AFTD.Kb.Tcs.BooleanAnalysisParseval
import AFTD.Kb.Tcs.G

/-!
# BoolFourier.parseval_identity

Topic: interactive   Node: fce8b6f9fef6

Provenance: helper lemma. TCSlib, `BoolFourier.parseval_identity`. Lean proof by Prastik Mohanraj, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/BLR/BoolFourier.lean (Copyright (c) 2026 Prastik Mohanraj. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Parseval's identity for the Walsh–Fourier expansion. Let $f : \{0,1\}^n \to \bbr$ be a real-valued function on the Boolean hypercube, and for
each subset $S \subseteq [n]$ let $\hat f(S) = \langle f, \chi_S\rangle$ be its Fourier
coefficient, where the inner product and expectation are taken with respect to the
uniform measure. Then the sum of the squared Fourier coefficients equals the squared
$L^2$ norm of $f$:
\[
  \sum_{S \subseteq [n]} \hat f(S)^2 \;=\; \|f\|_2^2 \;=\; \E\bigl[f^2\bigr].
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Finset BooleanAnalysis in
/-- States Parseval's identity for Boolean-cube Fourier coefficients. **Source:** [OD14, §1.4]. -/
lemma BoolFourier.parseval_identity {n : ℕ} (f : BoolFun n) :
    ∑ S : Finset (Fin n), (fourier_coeff f S) ^ 2 = L2_norm_sq f := by
  simp_rw [fourier_coeff_eq]
  rw [(parseval_identity_aux_hL2 f), ← parseval]

-- (f * g)̂(S) = f̂(S) · ĝ(S)
