import AFTD.Prelude

/-!
# instInvertibleMatrixValMemSubmonoidUnitaryGroup_quantumInfo

Topic: quantum   Node: 4bb29c68618e

Provenance: formalization of a published result. Source: QuantumInfo, `instInvertibleMatrixValMemSubmonoidUnitaryGroup_quantumInfo`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Isometry.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

instInvertibleMatrixValMemSubmonoidUnitaryGroup_quantumInfo
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped Matrix in
variable {d d₂ d₃ R : Type*} in
variable [Fintype d] [DecidableEq d] [Fintype d₂] [DecidableEq d₂] [Fintype d₃] [DecidableEq d₃] in
variable [CommRing R] [StarRing R] in
variable {𝕜 : Type*} [RCLike 𝕜] {A B : Matrix d d 𝕜} in
variable (U : Matrix.unitaryGroup d 𝕜) in
instance instInvertibleMatrixValMemSubmonoidUnitaryGroup_quantumInfo (U : Matrix.unitaryGroup d 𝕜) : Invertible U.val :=
  ⟨star U.val, U.2.1, U.2.2⟩
