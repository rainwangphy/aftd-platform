import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphSumChooseDegreeTwoLeChooseCardEdgeFinset
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# simple_graph_is_tree_card_sub_two_le_sum_choose_degree_le_choose

Topic: graphs   Node: 8826133b7d22

Provenance: formalization of a published result. Source: arXiv:2610.12109 (Sharp linear Turán remainders for cycle and edge extremality), Lemma 2.5, the two inequalities (the equality cases are stated as separate nodes).

For a tree T on k ≥ 2 vertices, σ₂(T) = ∑_v C(d_T(v),2) satisfies k − 2 ≤ σ₂(T) ≤ C(k−1,2).
-/

theorem simple_graph_is_tree_card_sub_two_le_sum_choose_degree_le_choose {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hT : G.IsTree)
    (hk : 2 ≤ Fintype.card V) :
    Fintype.card V - 2 ≤ ∑ v, (G.degree v).choose 2 ∧
      ∑ v, (G.degree v).choose 2 ≤ (Fintype.card V - 1).choose 2 := by
  have hE : G.edgeFinset.card + 1 = Fintype.card V := hT.card_edgeFinset
  refine ⟨?_, ?_⟩
  · have hsum := G.sum_degrees_eq_twice_card_edges
    have hz : ((Fintype.card V : ℤ) - 2) ≤ ∑ v, ((G.degree v).choose 2 : ℤ) := by
      have h1 : ∀ v, ((G.degree v : ℤ) - 1) ≤ ((G.degree v).choose 2 : ℤ) := by
        intro v
        generalize G.degree v = d
        rcases d with _ | m
        · simp
        · rw [Nat.choose_succ_succ, Nat.choose_one_right]
          push_cast
          omega
      calc ((Fintype.card V : ℤ) - 2) = ∑ v, ((G.degree v : ℤ) - 1) := by
            rw [Finset.sum_sub_distrib]
            simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
            have : (∑ v, (G.degree v : ℤ)) = 2 * G.edgeFinset.card := by exact_mod_cast hsum
            rw [this]
            have : (G.edgeFinset.card : ℤ) + 1 = Fintype.card V := by exact_mod_cast hE
            linarith
        _ ≤ _ := Finset.sum_le_sum fun v _ => h1 v
    have : ((Fintype.card V - 2 : ℕ) : ℤ) ≤ ((∑ v, (G.degree v).choose 2 : ℕ) : ℤ) := by
      push_cast
      rw [Nat.cast_sub hk]
      push_cast
      exact hz
    exact_mod_cast this
  · have h := simple_graph_sum_choose_degree_two_le_choose_card_edgeFinset G
    rwa [show G.edgeFinset.card = Fintype.card V - 1 by omega] at h
