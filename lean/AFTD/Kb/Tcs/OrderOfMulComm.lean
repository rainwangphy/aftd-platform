import AFTD.Prelude

/-!
# order_of_mul_comm

Topic: automata   Node: 2363d9d0d736

Provenance: helper lemma. folklore

For any two elements `x` and `y` in a group `G`, the element orders of `x * y` and `y * x` are equal.
-/

/-- Conjugate elements `x * y` and `y * x` in a group have the same order. -/
theorem order_of_mul_comm {G : Type*} [Group G] (x y : G) : orderOf (x * y) = orderOf (y * x) := by
  have h : y * x = MulAut.conj y (x * y) := by
    simp [MulAut.conj_apply, mul_assoc]
  rw [h, MulEquiv.orderOf_eq]
