import AFTD.Prelude
import AFTD.Kb.Tcs.BoolFourierBoolToPM1
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignMulSelf

/-!
# BoolFourier.BoolToPM1_sq

Topic: interactive   Node: 04f0f08d4d34

Provenance: helper lemma. TCSlib, `BoolFourier.BoolToPM1_sq`. Lean proof by Prastik Mohanraj, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/BLR/BoolFourier.lean (Copyright (c) 2026 Prastik Mohanraj. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Square of the Bool-to-$\pm 1$ embedding. For every Boolean value $b$, the image $\mathrm{BoolToPM1}(b)$ under the map sending
$\mathtt{false}$ to $1$ and $\mathtt{true}$ to $-1$ satisfies
$\mathrm{BoolToPM1}(b)\cdot\mathrm{BoolToPM1}(b) = 1$; that is, this $\pm 1$-valued
quantity squares to $1$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Finset BooleanAnalysis in
/-- Shows that every value of the `{±1}` encoding has square one. **Source:** [OD14, §1.3]. -/
lemma BoolFourier.BoolToPM1_sq (b : Bool) : BoolToPM1 b * BoolToPM1 b = 1 :=
  boolToSign_mul_self b
