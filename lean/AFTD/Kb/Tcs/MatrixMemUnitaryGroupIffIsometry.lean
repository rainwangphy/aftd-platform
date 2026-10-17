import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixIsometry

/-!
# Matrix.mem_unitaryGroup_iff_isometry

Topic: quantum   Node: 55230275f2ee

Provenance: formalization of a published result. Source: QuantumInfo, `Matrix.mem_unitaryGroup_iff_isometry`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Isometry.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Matrix.mem_unitaryGroup_iff_isometry
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped Matrix in
variable {d d₂ d₃ R : Type*} in
variable [Fintype d] [DecidableEq d] [Fintype d₂] [DecidableEq d₂] [Fintype d₃] [DecidableEq d₃] in
variable [CommRing R] [StarRing R] in
variable {𝕜 : Type*} [RCLike 𝕜] {A B : Matrix d d 𝕜} in
theorem Matrix.mem_unitaryGroup_iff_isometry (A : Matrix d d R) :
    A ∈ unitaryGroup d R ↔ A.Isometry ∧ Aᴴ.Isometry := by
  rw [Isometry, Isometry, conjTranspose_conjTranspose]
  rfl
