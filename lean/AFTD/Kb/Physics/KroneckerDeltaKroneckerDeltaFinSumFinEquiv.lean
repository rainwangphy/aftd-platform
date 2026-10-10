import AFTD.Prelude
import AFTD.Kb.Physics.KroneckerDeltaKroneckerDelta

/-!
# KroneckerDelta.kroneckerDelta_finSumFinEquiv

Topic: classical_mechanics   Node: 6dcaf0c8b92a

Provenance: formalization of a published result. Source: Physlib, `KroneckerDelta.kroneckerDelta_finSumFinEquiv`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/KroneckerDelta/Basic.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The Kronecker delta is invariant under the component-index equivalence `finSumFinEquiv`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open KroneckerDelta in
variable {α M : Type*} [DecidableEq α] in
/-- The Kronecker delta is invariant under the component-index equivalence `finSumFinEquiv`. -/
lemma KroneckerDelta.kroneckerDelta_finSumFinEquiv (a b : Fin 1 ⊕ Fin 3) :
    kroneckerDelta (finSumFinEquiv a) (finSumFinEquiv b) = kroneckerDelta a b := by
  simp only [kroneckerDelta, Equiv.apply_eq_iff_eq]
