import AFTD.Prelude
import AFTD.Kb.Tcs.BoolFourierBoolFun
import AFTD.Kb.Tcs.BoolFourierExpectation
import AFTD.Kb.Tcs.BoolFourierXorVec

/-!
# BoolFourier.convolution

Topic: interactive   Node: 28deb9248aaf

Provenance: formalization of a published result. Source: TCSlib, `BoolFourier.convolution`. Lean proof by Prastik Mohanraj, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/BLR/BoolFourier.lean (Copyright (c) 2026 Prastik Mohanraj. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The convolution of $f, g : \{0,1\}^n \to \mathbb{R}$ is the function
\[
  (f * g)(x) = \mathbb{E}_{y}\bigl[f(y)\,g(x \oplus y)\bigr].
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Finset BooleanAnalysis in
/-- Defines convolution of two real-valued Boolean-cube functions. **Source:** [OD14, §1.5]. -/
noncomputable def BoolFourier.convolution {n : ℕ} (f g : BoolFun n) : BoolFun n :=
  fun x => expectation (fun y => f y * g (xor_vec x y))
