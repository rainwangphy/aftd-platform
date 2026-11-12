import AFTD.Prelude
import AFTD.Kb.Tcs.BellmanValue
import AFTD.Kb.Tcs.PolicyValue
import AFTD.Kb.Tcs.EdgeArrivalProb
import AFTD.Kb.Tcs.CompatibleLabelings
import AFTD.Kb.Tcs.OnlineMatchingPolicy

/-!
# online_matching_policy_value_le_bellman

Topic: online_algorithms   Node: 401ff5570ab8

Provenance: helper lemma. arXiv:2611.13571, Lemma 5.1 proof

For a simple graph G on vertex set Fin n with decidable adjacency, every online matching policy pol : OnlineMatchingPolicy n satisfies policy_value G pol H U ≤ bellman_value G H U for all H : Finset (Sym2 (Fin n)) and U : Finset (Fin n).
-/

set_option maxHeartbeats 800000 in
lemma online_matching_policy_value_le_bellman_compatible_labelings_anti {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {H1 H2 : Finset (Sym2 (Fin n))} (hsub : H1 ⊆ H2) :
    compatible_labelings G H2 ≤ compatible_labelings G H1 := by
  unfold compatible_labelings
  apply Finset.card_le_card
  intro π hπ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ ⊢
  exact subset_trans hsub hπ

lemma online_matching_policy_value_le_bellman_card_le_of_compat_pos {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {H : Finset (Sym2 (Fin n))} (h : 0 < compatible_labelings G H) :
    H.card ≤ G.edgeFinset.card := by
  unfold compatible_labelings at h
  rw [Finset.card_pos] at h
  obtain ⟨π, hπ⟩ := h
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ
  calc H.card ≤ (G.map π.toEmbedding).edgeFinset.card := Finset.card_le_card hπ
    _ = G.edgeFinset.card := by
        rw [SimpleGraph.edgeFinset_card, SimpleGraph.edgeFinset_card]
        simp only [SimpleGraph.edgeSet_map]
        exact Set.card_image_of_injective _ (Sym2.map.injective π.toEmbedding.injective)

lemma online_matching_policy_value_le_bellman_edge_arrival_prob_nonneg {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (H : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n))
    (h : 0 < compatible_labelings G (insert e H)) :
    0 ≤ edge_arrival_prob G H e := by
  have hcard : H.card ≤ G.edgeFinset.card :=
    le_trans (Finset.card_le_card (Finset.subset_insert e H))
      (online_matching_policy_value_le_bellman_card_le_of_compat_pos G h)
  have hcompH : 0 < compatible_labelings G H :=
    lt_of_lt_of_le h
      (online_matching_policy_value_le_bellman_compatible_labelings_anti G (Finset.subset_insert e H))
  unfold edge_arrival_prob
  split_ifs with hden
  · exact le_refl 0
  · apply div_nonneg
    · exact Nat.cast_nonneg _
    · apply le_of_lt
      apply lt_of_le_of_ne _ (Ne.symm hden)
      apply mul_nonneg
      · exact sub_nonneg.mpr (by exact_mod_cast hcard)
      · exact Nat.cast_nonneg _

set_option maxHeartbeats 800000 in
lemma online_matching_policy_value_le_bellman_aux {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (pol : OnlineMatchingPolicy n) (k : ℕ) :
    ∀ (H : Finset (Sym2 (Fin n))) (U : Finset (Fin n)),
      policy_value.aux G pol k H U ≤ bellman_value.aux G k H U := by
  induction k with
  | zero =>
    intro H U
    rw [policy_value.aux.eq_1, bellman_value.aux.eq_1]
  | succ k ih =>
    intro H U
    rw [policy_value.aux.eq_2, bellman_value.aux.eq_2]
    apply Finset.sum_le_sum
    intro e _
    by_cases hguard : e ∉ H ∧ 0 < compatible_labelings G (insert e H)
    · rw [if_pos hguard, if_pos hguard]
      apply mul_le_mul_of_nonneg_left _
        (online_matching_policy_value_le_bellman_edge_arrival_prob_nonneg G H e hguard.2)
      by_cases hsub : e.toFinset ⊆ U
      · rw [if_pos hsub]
        by_cases hpol : pol H U e = true
        · rw [if_pos ⟨hsub, hpol⟩]
          apply le_trans _ (le_max_right _ _)
          linarith [ih (insert e H) (U \ e.toFinset)]
        · rw [if_neg (fun hc => hpol hc.2)]
          exact le_trans (ih (insert e H) U) (le_max_left _ _)
      · rw [if_neg hsub, if_neg (fun hc => hsub hc.1)]
        exact ih (insert e H) U
    · rw [if_neg hguard, if_neg hguard]

/-- Every online policy achieves at most the Bellman value from every state. -/
theorem online_matching_policy_value_le_bellman {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (pol : OnlineMatchingPolicy n)
    (H : Finset (Sym2 (Fin n))) (U : Finset (Fin n)) :
    policy_value G pol H U ≤ bellman_value G H U := by
  rw [policy_value.eq_1, bellman_value.eq_1]
  exact online_matching_policy_value_le_bellman_aux G pol
    (G.edgeFinset.card - H.card) H U
