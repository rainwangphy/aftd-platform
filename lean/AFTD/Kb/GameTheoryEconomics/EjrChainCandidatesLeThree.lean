import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsEjrCommittee
import AFTD.Kb.GameTheoryEconomics.EjrChainOfNestedCommittees
import AFTD.Kb.GameTheoryEconomics.IsEjrCommitteeZero
import AFTD.Kb.GameTheoryEconomics.EjrCommitteeUniv
import AFTD.Kb.GameTheoryEconomics.EjrAdjacentCommitteesExists
import AFTD.Kb.GameTheoryEconomics.EjrCommitteeExists

/-!
# ejr_chain_candidates_le_three

Topic: social_choice   Node: f8442f60d23c

Provenance: helper lemma. step towards ejr_committee_monotone_chain_exists

Every approval profile on at most three candidates admits an EJR committee chain.
-/

/-- Every approval profile on at most three candidates admits an EJR committee chain. -/
theorem ejr_chain_candidates_le_three (n m : ℕ) (A : Fin n → Finset (Fin m))
    (hn : 0 < n) (hm : m ≤ 3) :
    ∃ σ : Equiv.Perm (Fin m), ∀ k, k ≤ m →
      is_ejr_committee A k (Finset.univ.filter fun c => (σ c : ℕ) < k) := by
  apply ejr_chain_of_nested_committees
  interval_cases m
  · -- m = 0
    refine ⟨fun _ => ∅, rfl, ?_, ?_⟩
    · intro k hk; omega
    · intro k hk
      have hk0 : k = 0 := by omega
      subst hk0
      exact is_ejr_committee_zero A hn
  · -- m = 1
    refine ⟨fun k => if k = 0 then ∅ else Finset.univ, rfl, ?_, ?_⟩
    · intro k hk
      interval_cases k
      · simp
    · intro k hk
      interval_cases k
      · simpa using is_ejr_committee_zero A hn
      · simpa using ejr_committee_univ (m := 1) A hn
  · -- m = 2
    obtain ⟨W1, hW1⟩ := ejr_committee_exists n 2 A hn 1 (by norm_num)
    refine ⟨fun k => if k = 0 then ∅ else if k = 1 then W1 else Finset.univ, rfl, ?_, ?_⟩
    · intro k hk
      interval_cases k
      · simp
      · simp
    · intro k hk
      interval_cases k
      · simpa using is_ejr_committee_zero A hn
      · simpa using hW1
      · simpa using ejr_committee_univ (m := 2) A hn
  · -- m = 3
    obtain ⟨W1, W2, h12, hW1, hW2⟩ := ejr_adjacent_committees_exists A hn 1 (by norm_num)
    refine ⟨fun k => if k = 0 then ∅ else if k = 1 then W1 else if k = 2 then W2 else Finset.univ, rfl, ?_, ?_⟩
    · intro k hk
      interval_cases k
      · simp
      · simpa using h12
      · simp
    · intro k hk
      interval_cases k
      · simpa using is_ejr_committee_zero A hn
      · simpa using hW1
      · simpa using hW2
      · simpa using ejr_committee_univ (m := 3) A hn
