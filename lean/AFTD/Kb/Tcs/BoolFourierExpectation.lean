import AFTD.Prelude
import AFTD.Kb.Tcs.BoolFourierBoolFun

/-!
# BoolFourier.expectation

Topic: interactive   Node: 0572a3b4c30b

Provenance: formalization of a published result. Source: TCSlib, `BoolFourier.expectation`. Lean proof by Prastik Mohanraj, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/BLR/BoolFourier.lean (Copyright (c) 2026 Prastik Mohanraj. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For $f : \{0,1\}^n \to \mathbb{R}$, the uniform expectation is
\[
  \mathbb{E}[f] = \frac{1}{2^n} \sum_{x \in \{0,1\}^n} f(x).
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Finset BooleanAnalysis in
/-- Defines uniform expectation on the Boolean cube. **Source:** [OD14, §1.3]. -/
noncomputable def BoolFourier.expectation {n : ℕ} (f : BoolFun n) : ℝ :=
  (Finset.sum Finset.univ fun x => f x) / (2 : ℝ) ^ n

-- E[∏_i g_i(x_i)] = ∏_i (g_i(false) + g_i(true)) / 2
