import AFTD.Prelude
import AFTD.Kb.Tcs.BellmanValue
import AFTD.Kb.Tcs.OptimalOnlinePolicy
import AFTD.Kb.Tcs.PolicyValue
import AFTD.Kb.Tcs.EdgeArrivalProb
import AFTD.Kb.Tcs.CompatibleLabelings

/-!
# optimal_online_matching_policy_achieves_value

Topic: online_algorithms   Node: d45f94cb8734

Provenance: helper lemma. arXiv:2611.13571, Lemma 5.1 proof

For a simple graph G on vertex set Fin n with decidable adjacency, the optimal online matching policy optimal_online_policy G achieves policy_value G (optimal_online_policy G) H U = bellman_value G H U for all H : Finset (Sym2 (Fin n)) and U : Finset (Fin n).
-/

lemma optimal_online_matching_policy_achieves_value_card_sub_insert {α : Type*} [DecidableEq α]
    (s : Finset α) (M : ℕ) (k : ℕ) (x : α)
    (h_sub : M - s.card = k + 1) (hx : x ∉ s) :
    M - (insert x s).card = k := by
  rw [Finset.card_insert_of_notMem hx]
  omega

lemma optimal_online_matching_policy_achieves_value_aux {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) :
    ∀ (H : Finset (Sym2 (Fin n))) (U : Finset (Fin n)),
      G.edgeFinset.card - H.card = k →
      policy_value.aux G (optimal_online_policy G) k H U = bellman_value.aux G k H U := by
  induction' k with k ih
  · intro H U _
    rfl
  · intro H U hH
    show (∑ e ∈ (Finset.univ : Finset (Sym2 (Fin n))), _) = (∑ e ∈ (Finset.univ : Finset (Sym2 (Fin n))), _)
    apply Finset.sum_congr rfl
    intro e _
    by_cases he : e ∉ H ∧ 0 < compatible_labelings G (insert e H)
    · rw [if_pos he, if_pos he]
      congr 1
      have hk : G.edgeFinset.card - (insert e H).card = k :=
        optimal_online_matching_policy_achieves_value_card_sub_insert H _ k e hH he.1
      have ih1 := ih (insert e H) U hk
      have ih2 := ih (insert e H) (U \ e.toFinset) hk
      have h_bv1 : bellman_value G (insert e H) U = bellman_value.aux G k (insert e H) U := by
        change bellman_value.aux G (G.edgeFinset.card - (insert e H).card) (insert e H) U = _
        rw [hk]
      have h_bv2 : bellman_value G (insert e H) (U \ e.toFinset) = bellman_value.aux G k (insert e H) (U \ e.toFinset) := by
        change bellman_value.aux G (G.edgeFinset.card - (insert e H).card) (insert e H) (U \ e.toFinset) = _
        rw [hk]
      rw [ih1, ih2]
      unfold optimal_online_policy
      rw [h_bv1, h_bv2]
      by_cases hU : e.toFinset ⊆ U
      · simp only [hU, true_and]
        by_cases hle : bellman_value.aux G k (insert e H) U ≤ 1 + bellman_value.aux G k (insert e H) (U \ e.toFinset)
        · simp [hle]
        · have hle' : 1 + bellman_value.aux G k (insert e H) (U \ e.toFinset) ≤ bellman_value.aux G k (insert e H) U :=
            le_of_lt (not_le.mp hle)
          simp [hle, hle']
      · simp only [hU, false_and, if_false]
    · rw [if_neg he, if_neg he]

/-- The optimal online policy achieves the Bellman value from every state. -/
theorem optimal_online_matching_policy_achieves_value {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (H : Finset (Sym2 (Fin n))) (U : Finset (Fin n)) :
    policy_value G (optimal_online_policy G) H U = bellman_value G H U := by
  change policy_value.aux G (optimal_online_policy G) (G.edgeFinset.card - H.card) H U =
    bellman_value.aux G (G.edgeFinset.card - H.card) H U
  exact optimal_online_matching_policy_achieves_value_aux G (G.edgeFinset.card - H.card) H U rfl
