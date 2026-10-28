import AFTD.Prelude

/-!
# is_two_type_allocation_exists

Topic: fair_division   Node: 291ab6e0d1fe

Provenance: helper lemma. arXiv:2610.19099

For any positive number of agents n and any item counts a and b, there exists a complete count allocation of the two types of goods.
-/

/-- A complete count allocation of two types of goods always exists when n > 0. -/
theorem is_two_type_allocation_exists (n a b : ℕ) (hn : 0 < n) :
    ∃ x y : Fin n → ℕ, (∑ i, x i = a) ∧ (∑ i, y i = b) := by
  refine ⟨fun i => if i = ⟨0, hn⟩ then a else 0,
          fun i => if i = ⟨0, hn⟩ then b else 0, ?_, ?_⟩
  · rw [Finset.sum_ite_eq']; simp
  · rw [Finset.sum_ite_eq']; simp
