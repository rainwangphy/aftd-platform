import AFTD.Prelude
import AFTD.Kb.Tcs.BoolFourierBoolFun
import AFTD.Kb.Tcs.BoolFourierL2NormSq
import AFTD.Kb.Tcs.BoolFourierExpectationEqExpect
import AFTD.Kb.Tcs.BooleanAnalysisInnerProduct

/-!
# BoolFourier.parseval_identity_aux_hL2

Topic: interactive   Node: 0d7d9b10a2e4

Provenance: helper lemma. TCSlib, `BoolFourier.parseval_identity_aux_hL2`. Lean proof by Prastik Mohanraj, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/BLR/BoolFourier.lean (Copyright (c) 2026 Prastik Mohanraj. All rights reserved, Apache-2.0); 1 adapted; compiled here.

$L^2$ norm squared as a self inner product. Let $f : \{0,1\}^n \to \bbr$ be a real-valued function on the Boolean hypercube, and
equip such functions with the uniform-measure inner product $\langle g, h \rangle =
2^{-n}\sum_{x \in \{0,1\}^n} g(x)\,h(x)$. Then the squared $L^2$ norm of $f$ equals the
inner product of $f$ with itself:
\[
  \|f\|_2^2 \;=\; \langle f, f \rangle.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Finset BooleanAnalysis in
lemma BoolFourier.parseval_identity_aux_hL2 {n : Nat} (f : BoolFun n) : L2_norm_sq f = (BooleanAnalysis.innerProduct f f) := by
  unfold L2_norm_sq BooleanAnalysis.innerProduct
  rw [expectation_eq_expect]
  congr 1; funext x; ring
