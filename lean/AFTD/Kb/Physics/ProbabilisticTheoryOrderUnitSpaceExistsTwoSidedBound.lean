import AFTD.Prelude
import AFTD.Kb.Physics.ProbabilisticTheoryOrderUnitSpace
import AFTD.Kb.Physics.ProbabilisticTheoryOrderedVectorSpace

/-!
# ProbabilisticTheory.OrderUnitSpace.exists_two_sided_bound

Topic: quantum_mechanics   Node: 7a5d28ef4bf7

Provenance: formalization of a published result. Source: Physlib, `ProbabilisticTheory.OrderUnitSpace.exists_two_sided_bound`. Lean proof by Tom Ole Diem, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ProbabilisticTheory/OrderUnit/Basic.lean (Copyright (c) 2026 Tom Ole Diem. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Every element is bounded on both sides by a natural multiple of the order unit.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ProbabilisticTheory in
variable {E : Type*} [OrderUnitSpace E] in
/-- Every element is bounded on both sides by a natural multiple of the order unit. -/
lemma ProbabilisticTheory.OrderUnitSpace.exists_two_sided_bound (A : E) : ∃ n : ℕ, -(n • (1 : E)) ≤ A ∧ A ≤ n • (1 : E) := by
  obtain ⟨n, hn⟩ := exists_nsmul_one_le A
  obtain ⟨m, hm⟩ := exists_nsmul_one_le (-A)
  refine ⟨max n m, ?_, hn.trans (nsmul_le_nsmul_left one_nonneg (le_max_left n m))⟩
  exact neg_le_of_neg_le <| hm.trans (nsmul_le_nsmul_left one_nonneg (le_max_right n m))
