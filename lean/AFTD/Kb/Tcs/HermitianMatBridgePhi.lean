import AFTD.Prelude

/-!
# HermitianMatBridge.Φ

Topic: quantum   Node: e841933cf1b5

Provenance: formalization of a published result. Source: QuantumInfo, `HermitianMatBridge.Φ`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HermitianMat/LiebConcavity.lean (Copyright (c) 2026 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Abbreviation for the star algebra isomorphism.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {d : Type*} [Fintype d] [DecidableEq d] in
/-- Abbreviation for the star algebra isomorphism. -/
noncomputable abbrev HermitianMatBridge.Φ : Matrix d d ℂ ≃⋆ₐ[ℂ] (EuclideanSpace ℂ d →L[ℂ] EuclideanSpace ℂ d) :=
  Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ)
