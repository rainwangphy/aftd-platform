import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsEjrCommitteeIffCandidateSubsets
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.IsEjrCommittee

/-!
# ejr_good_of_low_support_candidate

Topic: social_choice   Node: 4b8c4b537971

Provenance: helper lemma. step towards ejr_committee_monotone_chain_exists

If candidate c is approved by fewer than n/m voters (m times its supporter count is below n), then for any k-committee P with c not in P, EJR holds as soon as it holds for all demand-sets T not containing c.
-/

/-- A low-support candidate imposes no EJR constraint: subsets T containing it are automatically satisfied. -/
theorem ejr_good_of_low_support_candidate (n m : ℕ) (A : Fin n → Finset (Fin m)) (hn : 0 < n)
    (c : Fin m) (hc : m * (Finset.univ.filter fun i => c ∈ A i).card < n)
    (P : Finset (Fin m)) (hp : c ∉ P) (k : ℕ) (hkP : P.card = k)
    (h : ∀ T : Finset (Fin m), T.Nonempty → c ∉ T →
      (Finset.univ.filter fun i => T ⊆ A i ∧ (A i ∩ P).card < T.card).card * k < T.card * n) :
    is_ejr_committee A k P := by
  rw [is_ejr_committee_iff_candidate_subsets]
  refine ⟨hkP, fun T hT => ?_⟩
  by_cases hcT : c ∈ T
  · have hsub : (Finset.univ.filter fun i => T ⊆ A i ∧ (A i ∩ P).card < T.card) ⊆
        (Finset.univ.filter fun i => c ∈ A i) := by
      intro i hi
      rw [Finset.mem_filter] at hi ⊢
      refine ⟨hi.1, hi.2.1 hcT⟩
    have hcard : (Finset.univ.filter fun i => T ⊆ A i ∧ (A i ∩ P).card < T.card).card ≤
        (Finset.univ.filter fun i => c ∈ A i).card :=
      Finset.card_le_card hsub
    have hk_le_m : k ≤ m := by
      rw [← hkP]
      have : P.card ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_le_univ P
      simpa using this
    have h1 : (Finset.univ.filter fun i => T ⊆ A i ∧ (A i ∩ P).card < T.card).card * k ≤
        (Finset.univ.filter fun i => c ∈ A i).card * m :=
      Nat.mul_le_mul hcard hk_le_m
    have h2 : (Finset.univ.filter fun i => c ∈ A i).card * m < n := by
      rw [mul_comm]
      exact hc
    have h3 : n ≤ T.card * n := by
      have : 1 ≤ T.card := hT.card_pos
      calc n = 1 * n := by rw [one_mul]
      _ ≤ T.card * n := Nat.mul_le_mul_right n this
    linarith
  · exact h T hT hcT
