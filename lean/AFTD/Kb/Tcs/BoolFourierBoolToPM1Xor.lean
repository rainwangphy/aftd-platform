import AFTD.Prelude
import AFTD.Kb.Tcs.BoolFourierBoolToPM1
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSign

/-!
# BoolFourier.BoolToPM1_xor

Topic: interactive   Node: ca92f6ec1de0

Provenance: helper lemma. TCSlib, `BoolFourier.BoolToPM1_xor`. Lean proof by Prastik Mohanraj, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/BLR/BoolFourier.lean (Copyright (c) 2026 Prastik Mohanraj. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

XOR as multiplication under the $\pm 1$ embedding. Let $\mathrm{BoolToPM1} : \mathrm{Bool} \to \bbr$ be the map sending $\mathtt{false}$ to
$1$ and $\mathtt{true}$ to $-1$. Then for all Booleans $a$ and $b$,
\[
  \mathrm{BoolToPM1}(a \oplus b) = \mathrm{BoolToPM1}(a)\cdot\mathrm{BoolToPM1}(b),
\]
so the exclusive-or $a \oplus b$ is carried to the ordinary product in
$\{-1,1\}\subset\bbr$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Finset BooleanAnalysis in
/-- Shows that the `{±1}` encoding converts XOR into multiplication. **Source:** [OD14, §1.3]. -/
lemma BoolFourier.BoolToPM1_xor (a b : Bool) :
    BoolToPM1 (Bool.xor a b) = BoolToPM1 a * BoolToPM1 b := by
  cases a <;> cases b <;> simp [BoolToPM1, boolToSign, Bool.xor]
