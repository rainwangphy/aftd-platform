import AFTD.Prelude
import AFTD.Kb.Tcs.BoolFourierBoolFun
import AFTD.Kb.Tcs.BoolFourierCharS
import AFTD.Kb.Tcs.BoolFourierInnerProduct

/-!
# BoolFourier.fourier_coeff

Topic: interactive   Node: a6550ea16f8f

Provenance: formalization of a published result. Source: TCSlib, `BoolFourier.fourier_coeff`. Lean proof by Prastik Mohanraj, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/BLR/BoolFourier.lean (Copyright (c) 2026 Prastik Mohanraj. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The Fourier coefficient of $f : \{0,1\}^n \to \mathbb{R}$ at $S \subseteq [n]$ is
\[
  \hat f(S) = \langle f, \chi_S \rangle.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Finset BooleanAnalysis in
/-- Defines the Fourier coefficient of a Boolean-cube function at a character. **Source:** [OD14, §1.3]. -/
noncomputable def BoolFourier.fourier_coeff {n : ℕ} (f : BoolFun n) (S : Finset (Fin n)) : ℝ :=
  inner_product f (char_S S)
