import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsCondorcetWinningSet

/-!
# condorcet_winning_set_of_bottom_three_majority

Topic: social_choice   Node: 871174862060

Provenance: helper lemma. step towards condorcet_dimension_le_three

If S is a set of exactly three candidates and every candidate a outside S is ranked below all but at most two candidates by a strict majority of voters, then S is a Condorcet winning set.
-/

/-- Dual of the top-choice cover: a 3-set is winning as soon as every outside candidate sits in the bottom three of a strict majority of voters. -/
theorem condorcet_winning_set_of_bottom_three_majority {n m : ℕ} (P : Fin n → Equiv.Perm (Fin m))
    (S : Finset (Fin m)) (hS : S.card = 3)
    (h : ∀ a, a ∉ S → n < 2 * (Finset.univ.filter fun v =>
      (Finset.univ.filter fun c => P v a < P v c).card ≤ 2).card) :
    is_condorcet_winning_set P S := by
  intro a ha
  let B := Finset.univ.filter (fun v : Fin n =>
    (Finset.univ.filter fun c => P v a < P v c).card ≤ 2)
  let bad := Finset.univ.filter (fun v : Fin n => ∀ b ∈ S, P v a < P v b)
  have h_disj : Disjoint bad B := by
    rw [Finset.disjoint_left]
    intro v hv
    rw [Finset.mem_filter] at hv ⊢
    intro ⟨_, h2⟩
    have h_sub : S ⊆ Finset.univ.filter (fun c => P v a < P v c) := by
      intro b hb
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hv.2 b hb⟩
    have h_le := Finset.card_le_card h_sub
    rw [hS] at h_le
    omega
  have h_card_add : bad.card + B.card ≤ n := by
    have h_union : bad.card + B.card = (bad ∪ B).card := (Finset.card_union_of_disjoint h_disj).symm
    rw [h_union]
    have h_le := Finset.card_le_univ (bad ∪ B)
    simp only [Fintype.card_fin] at h_le
    exact h_le
  have hB : n < 2 * B.card := h a ha
  show 2 * bad.card < n
  omega
