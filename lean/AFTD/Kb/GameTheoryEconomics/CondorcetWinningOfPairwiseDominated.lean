import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsCondorcetWinningSet

/-!
# condorcet_winning_of_pairwise_dominated

Topic: social_choice   Node: 2ff9bfc3b639

Provenance: helper lemma. step towards condorcet_dimension_le_three

If every candidate outside S is pairwise strictly majority-defeated by some candidate in S, then S is a Condorcet winning set.
-/

/-- If every candidate outside S is pairwise majority-defeated by some candidate in S, then S is a Condorcet winning set. -/
theorem condorcet_winning_of_pairwise_dominated {n m : ℕ} (P : Fin n → Equiv.Perm (Fin m))
    (S : Finset (Fin m))
    (h : ∀ a, a ∉ S → ∃ b ∈ S, 2 * (Finset.univ.filter fun v => P v a < P v b).card < n) :
    is_condorcet_winning_set P S := by
  intro a ha
  obtain ⟨b, hbS, hb⟩ := h a ha
  have hsub : (Finset.univ.filter fun v => ∀ c ∈ S, P v a < P v c) ⊆
      (Finset.univ.filter fun v => P v a < P v b) := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact hv b hbS
  have := Finset.card_le_card hsub
  omega
