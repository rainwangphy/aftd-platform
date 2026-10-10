import AFTD.Prelude
import AFTD.Kb.Physics.MatrixDetAddRankOneAux

/-!
# Matrix.det_add_rankOne

Topic: classical_mechanics   Node: 1dbf5b1ba411

Provenance: formalization of a published result. Source: Physlib, `Matrix.det_add_rankOne`. Lean proof by Robert Sneiderman, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/KroneckerDelta/Contraction.lean (Copyright (c) 2026 Robert Sneiderman. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Rank-one determinant update** (the ring-general matrix determinant lemma for an outer product, valid even when `A` is singular). Adding the rank-one matrix `w ⊗ b` to `A` changes the determinant by `∑ i, w i * det (A.updateRow i b)`. Mathlib only provides this when `det A` is a unit (`Matrix.det_add_replicateCol_mul_replicateRow`); the singular case is needed here because Kronecker-delta matrices are typically singular.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
/-- **Rank-one determinant update** (the ring-general matrix determinant lemma for an outer product, valid even when `A` is singular). Adding the rank-one matrix `w ⊗ b` to `A` changes the determinant by `∑ i, w i * det (A.updateRow i b)`. Mathlib only provides this when `det A` is a unit (`Matrix.det_add_replicateCol_mul_replicateRow`); the singular case is needed here because Kronecker-delta matrices are typically singular. -/
lemma Matrix.det_add_rankOne {ι : Type*} [DecidableEq ι] [Fintype ι] {R : Type*}
    [CommRing R] (A : Matrix ι ι R) (w b : ι → R) :
    (A + Matrix.of fun i j => w i * b j).det = A.det + ∑ i, w i * (A.updateRow i b).det := by
  have h := det_add_rankOne_aux A w b Finset.univ
  simpa using h
