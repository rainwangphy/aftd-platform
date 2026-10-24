import AFTD.Prelude

/-!
# outside_voters_subset_top_choices_compl

Topic: social_choice   Node: 2c8c025d2a29

Provenance: helper lemma. step towards condorcet_dimension_le_three

For any candidate set S and candidate x, any voter who ranks x strictly above every member of S has their top-choice candidate outside S.
-/

/-- Any voter ranking x above every candidate in S must have their top choice outside S. -/
theorem outside_voters_subset_top_choices_compl {n m : ℕ} (P : Fin n → Equiv.Perm (Fin m))
    (S : Finset (Fin m)) (x : Fin m) (hm : 0 < m) :
    (Finset.univ.filter fun v => ∀ c ∈ S, P v x < P v c) ⊆
      Finset.univ.filter fun v => (P v).symm ⟨0, hm⟩ ∉ S := by
  intro v hv
  rw [Finset.mem_filter] at hv ⊢
  refine ⟨hv.1, fun h_top_in_S => ?_⟩
  have h_lt := hv.2 ((P v).symm ⟨0, hm⟩) h_top_in_S
  rw [Equiv.apply_symm_apply] at h_lt
  exact Nat.not_lt_zero _ h_lt
