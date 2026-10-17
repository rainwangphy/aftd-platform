import AFTD.Prelude

/-!
# Matrix.PosDef.toLin_ker_eq_bot

Topic: quantum   Node: 1910cf0273b7

Provenance: formalization of a published result. Source: QuantumInfo, `Matrix.PosDef.toLin_ker_eq_bot`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Matrix.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Matrix.PosDef.toLin_ker_eq_bot
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix Matrix.PosDef in
open BigOperators in
variable {n 𝕜 : Type*} in
variable [RCLike 𝕜] [DecidableEq n] in
open scoped ComplexOrder MatrixOrder in
open scoped ComplexOrder in
variable {n m 𝕜 : Type*} in
variable [Fintype n] [RCLike 𝕜] [DecidableEq n] in
variable {A : Matrix n n 𝕜} in
theorem Matrix.PosDef.toLin_ker_eq_bot (hA : A.PosDef) : LinearMap.ker A.toLin' = ⊥ := by
  ext v
  rw [Matrix.posDef_iff_dotProduct_mulVec] at hA
  have := @hA.right v
  grind [mulVec_zero, dotProduct_zero, LinearMap.mem_ker, toLin'_apply, Submodule.mem_bot]
