import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsEjrCommitteeIffCandidateSubsets
import AFTD.Kb.GameTheoryEconomics.IsEjrCommittee

/-!
# ejr_committee_univ

Topic: social_choice   Node: c08ca61ee1fa

Provenance: helper lemma. step towards ejr_committee_monotone_chain_exists

For every approval profile with at least one voter, the committee consisting of all m candidates satisfies EJR at committee size m.
-/

/-- For a nonempty electorate the full committee satisfies EJR at committee size m. -/
theorem ejr_committee_univ {n m : ℕ} (A : Fin n → Finset (Fin m)) (hn : 0 < n) :
    is_ejr_committee A m Finset.univ := by
  rw [is_ejr_committee_iff_candidate_subsets]
  constructor
  · simp
  · intro T hT
    have hfilter :
        (Finset.univ.filter fun i => T ⊆ A i ∧ (A i ∩ Finset.univ).card < T.card) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro i _
      rw [Finset.inter_univ]
      rintro ⟨hsub, hlt⟩
      exact absurd (Finset.card_le_card hsub) (not_le.mpr hlt)
    rw [hfilter]
    simp only [Finset.card_empty, Nat.zero_mul]
    exact Nat.mul_pos (Finset.card_pos.mpr hT) hn
