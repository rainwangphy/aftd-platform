import AFTD.Prelude
import AFTD.Kb.Tcs.LinearEquivEuclideanOfRelabel
import AFTD.Kb.Tcs.LinearEquivOfRelabelRefl
import AFTD.Kb.Tcs.LinearEquivEuclideanOfRelabelRefl

/-!
# Matrix.reindex_toEuclideanLin

Topic: quantum   Node: 40f725ddbd45

Provenance: formalization of a published result. Source: QuantumInfo, `Matrix.reindex_toEuclideanLin`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/LinearEquiv.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Matrix.reindex_toEuclideanLin
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {d d₁ d₂ d₃ R 𝕜 : Type*} [RCLike 𝕜] in
variable {R : Type*} [CommSemiring R] in
variable [Fintype d] [DecidableEq d] in
variable [Fintype d₂] [DecidableEq d₂] in
theorem Matrix.reindex_toEuclideanLin (e : d₁ ≃ d₃) (f : d₂ ≃ d) (M : Matrix d₁ d₂ 𝕜) :
    (M.reindex e f).toEuclideanLin = (LinearEquiv.euclideanOfRelabel 𝕜 e.symm) ∘ₗ
      M.toEuclideanLin ∘ₗ (LinearEquiv.euclideanOfRelabel 𝕜 f) := by
  ext
  simp [mulVec, dotProduct, Equiv.piCongrLeft_apply]
