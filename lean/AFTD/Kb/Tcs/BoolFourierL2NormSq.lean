import AFTD.Prelude
import AFTD.Kb.Tcs.BoolFourierBoolFun
import AFTD.Kb.Tcs.BoolFourierExpectation

/-!
# BoolFourier.L2_norm_sq

Topic: interactive   Node: 3938412f9847

Provenance: formalization of a published result. Source: TCSlib, `BoolFourier.L2_norm_sq`. Lean proof by Prastik Mohanraj, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/BLR/BoolFourier.lean (Copyright (c) 2026 Prastik Mohanraj. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The squared $L^2$ norm of $f : \{0,1\}^n \to \mathbb{R}$ is
\[
  \|f\|_2^2 = \mathbb{E}[f^2]
  = \frac{1}{2^n}\sum_{x} f(x)^2.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Finset BooleanAnalysis in
/-- Defines the squared `L²` norm on the Boolean cube. **Source:** [OD14, §1.3]. -/
noncomputable def BoolFourier.L2_norm_sq {n : ℕ} (f : BoolFun n) : ℝ :=
  expectation (fun x => f x ^ 2)
