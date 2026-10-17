import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixIsometry

/-!
# Matrix.reindex_one_isometry

Topic: quantum   Node: da68cec137b2

Provenance: formalization of a published result. Source: QuantumInfo, `Matrix.reindex_one_isometry`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Isometry.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Matrix.reindex_one_isometry
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped Matrix in
variable {d d₂ d₃ R : Type*} in
variable [Fintype d] [DecidableEq d] [Fintype d₂] [DecidableEq d₂] [Fintype d₃] [DecidableEq d₃] in
variable [CommRing R] [StarRing R] in
variable {𝕜 : Type*} [RCLike 𝕜] {A B : Matrix d d 𝕜} in
omit [Fintype d₃] [DecidableEq d₂] in
theorem Matrix.reindex_one_isometry (e : d ≃ d₂) (f : d ≃ d₃) :
    (reindex (α := R) e f 1).Isometry := by
  -- Since $e$ and $f$ are bijections, the reindexing of the identity matrix by $e$ and $f$ is a permutation matrix, which is unitary.
  have h_perm : ∀ (e : d ≃ d₂) (f : d ≃ d₃), (Matrix.reindex e f (1 : Matrix d d R)).Isometry := by
    intro e f
    simp [Matrix.Isometry]
  exact h_perm e f
