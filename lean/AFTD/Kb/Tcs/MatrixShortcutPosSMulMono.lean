import AFTD.Prelude

/-!
# Matrix._shortcut_posSMulMono

Topic: quantum   Node: fbff77e76812

Provenance: formalization of a published result. Source: QuantumInfo, `Matrix._shortcut_posSMulMono`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Matrix.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Matrix._shortcut_posSMulMono
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open BigOperators in
variable {n 𝕜 : Type*} in
variable [RCLike 𝕜] [DecidableEq n] in
open scoped ComplexOrder MatrixOrder in
open MatrixOrder in
variable {d : Type*} [Fintype d] in
lemma Matrix._shortcut_posSMulMono : PosSMulMono ℝ (Matrix d d ℂ) :=
  inferInstance
