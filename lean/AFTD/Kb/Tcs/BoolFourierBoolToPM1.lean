import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSign

/-!
# BoolFourier.BoolToPM1

Topic: interactive   Node: 750a33a21832

Provenance: formalization of a published result. Source: TCSlib, `BoolFourier.BoolToPM1`. Lean proof by Prastik Mohanraj, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/BLR/BoolFourier.lean (Copyright (c) 2026 Prastik Mohanraj. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The map $\mathrm{BoolToPM1} : \mathrm{Bool} \to \mathbb{R}$ sends $\mathtt{false}$
to $1$ and $\mathtt{true}$ to $-1$, realising the standard identification
$\{0,1\} \cong \{\pm 1\}$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Finset BooleanAnalysis in
/-- Names the standard embedding of Boolean values into `{±1} ⊂ ℝ`. **Source:** [OD14, §1.3]. -/
abbrev BoolFourier.BoolToPM1 : Bool → ℝ := boolToSign
