import AFTD.Prelude
import AFTD.Kb.Tcs.IsAdditiveBasis

/-!
# not_is_additive_basis_zero

Topic: combinatorics   Node: c0531ed20d91

Provenance: helper lemma. scout/2610-13103-additive-bases-and-the-zero-sum-invariant-mathsf-n-g-for-gr.md:91

For any nontrivial additive commutative group G, the empty multiset 0 : Multiset G is not an additive basis (¬ IsAdditiveBasis (0 : Multiset G)).
-/

/-- The empty multiset is not an additive basis for any nontrivial additive commutative group. -/
theorem not_is_additive_basis_zero {G : Type*} [AddCommGroup G] [Nontrivial G] : ¬ IsAdditiveBasis (0 : Multiset G) := by
  intro h
  obtain ⟨T, hT1, hT2, _⟩ := h 0
  exact hT2 (nonpos_iff_eq_zero.mp hT1)
