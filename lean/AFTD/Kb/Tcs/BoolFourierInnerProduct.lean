import AFTD.Prelude
import AFTD.Kb.Tcs.BoolFourierBoolFun
import AFTD.Kb.Tcs.BoolFourierExpectation

/-!
# BoolFourier.inner_product

Topic: interactive   Node: cefcff7dab1a

Provenance: formalization of a published result. Source: TCSlib, `BoolFourier.inner_product`. Lean proof by Prastik Mohanraj, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/BLR/BoolFourier.lean (Copyright (c) 2026 Prastik Mohanraj. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The inner product of $f, g : \{0,1\}^n \to \mathbb{R}$ is
\[
  \langle f, g \rangle = \mathbb{E}[f \cdot g]
  = \frac{1}{2^n}\sum_{x} f(x)\,g(x).
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Finset BooleanAnalysis in
/-- Defines the Boolean-cube inner product by uniform expectation. **Source:** [OD14, §1.3]. -/
noncomputable def BoolFourier.inner_product {n : ℕ} (f g : BoolFun n) : ℝ :=
  expectation (fun x => f x * g x)
