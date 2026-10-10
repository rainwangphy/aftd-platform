import AFTD.Prelude
import AFTD.Kb.Physics.KroneckerDeltaGeneralizedKroneckerDelta
import AFTD.Kb.Physics.KroneckerDeltaKroneckerDelta

/-!
# KroneckerDelta.generalizedKroneckerDelta_comp_perm

Topic: classical_mechanics   Node: 380ef1bafbad

Provenance: formalization of a published result. Source: Physlib, `KroneckerDelta.generalizedKroneckerDelta_comp_perm`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/KroneckerDelta/Basic.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Simultaneously reindexing the upper and lower slots of a generalized Kronecker delta by the same permutation leaves it unchanged.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open KroneckerDelta in
variable {α M : Type*} [DecidableEq α] in
open Matrix in
/-- Simultaneously reindexing the upper and lower slots of a generalized Kronecker delta by the same permutation leaves it unchanged. -/
@[simp]
lemma KroneckerDelta.generalizedKroneckerDelta_comp_perm {α ι : Type} [DecidableEq α] [DecidableEq ι]
    [Fintype ι] (μ ν : ι → α) (e : Equiv.Perm ι) :
    generalizedKroneckerDelta (μ ∘ e) (ν ∘ e) = generalizedKroneckerDelta μ ν := by
  show (Matrix.submatrix
      (Matrix.of fun i j => ((kroneckerDelta (μ i) (ν j) : ℕ) : ℤ)) e e).det =
    (Matrix.of fun i j => ((kroneckerDelta (μ i) (ν j) : ℕ) : ℤ)).det
  exact Matrix.det_submatrix_equiv_self e _
