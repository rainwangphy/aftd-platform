import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsTreeCardSubTwoLeSumChooseDegreeLeChoose
import AFTD.Kb.Tcs.PathGraphDegreeLeTwo
import AFTD.Kb.Tcs.SimpleGraphConnectedDegreePos
import AFTD.Kb.Tcs.SimpleGraphIsTreeNonemptyIsoPathGraphOfDegreeLeTwo
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# simple_graph_is_tree_sum_choose_degree_eq_iff_path

Topic: graphs   Node: 97e9dfac3e2e

Provenance: formalization of a published result. Source: arXiv:2610.12109 (Sharp linear Turán remainders for cycle and edge extremality), Lemma 2.5, equality case of the lower bound.

For a tree T on k ≥ 2 vertices, σ₂(T) = k − 2 if and only if T is isomorphic to the path P_k.
-/

theorem simple_graph_is_tree_sum_choose_degree_eq_iff_path {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hT : G.IsTree)
    (hk : 2 ≤ Fintype.card V) :
    ∑ v, (G.degree v).choose 2 = Fintype.card V - 2 ↔
      Nonempty (G ≃g SimpleGraph.pathGraph (Fintype.card V)) := by
  classical
  have hE : G.edgeFinset.card + 1 = Fintype.card V := hT.card_edgeFinset
  have hsumdeg : (∑ v, (G.degree v : ℤ)) = 2 * (Fintype.card V - 1) := by
    have := G.sum_degrees_eq_twice_card_edges
    have h' : (∑ v, (G.degree v : ℤ)) = 2 * G.edgeFinset.card := by exact_mod_cast this
    rw [h']
    have : (G.edgeFinset.card : ℤ) + 1 = Fintype.card V := by exact_mod_cast hE
    linarith
  -- ∑ (d − 1) = k − 2 in ℤ
  have hsub1 : (∑ v, ((G.degree v : ℤ) - 1)) = Fintype.card V - 2 := by
    rw [Finset.sum_sub_distrib, hsumdeg]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    ring
  have hle : ∀ v, ((G.degree v : ℤ) - 1) ≤ ((G.degree v).choose 2 : ℤ) := by
    intro v
    generalize G.degree v = d
    rcases d with _ | m
    · simp
    · rw [Nat.choose_succ_succ, Nat.choose_one_right]
      push_cast
      omega
  constructor
  · intro hsum
    apply simple_graph_is_tree_nonempty_iso_path_graph_of_degree_le_two G hT
    have hz : (∑ v, ((G.degree v).choose 2 : ℤ)) = ∑ v, ((G.degree v : ℤ) - 1) := by
      rw [hsub1]
      have : ((∑ v, (G.degree v).choose 2 : ℕ) : ℤ) = ((Fintype.card V - 2 : ℕ) : ℤ) := by
        rw [hsum]
      push_cast at this
      rw [this]
      omega
    have heach := (Finset.sum_eq_sum_iff_of_le (fun v _ => hle v)).1 hz.symm
    intro v
    have hv := heach v (Finset.mem_univ v)
    by_contra hlt
    push Not at hlt
    obtain ⟨m, hm⟩ : ∃ m, G.degree v = m + 3 := ⟨G.degree v - 3, by omega⟩
    rw [hm, Nat.choose_succ_succ, Nat.choose_one_right] at hv
    have hpos : 0 < (m + 2).choose 2 := Nat.choose_pos (by omega)
    push_cast at hv
    omega
  · rintro ⟨f⟩
    have hdeg2 : ∀ v, G.degree v ≤ 2 := by
      intro v
      calc G.degree v ≤ (SimpleGraph.pathGraph (Fintype.card V)).degree (f v) := by
            rw [← SimpleGraph.card_neighborFinset_eq_degree,
              ← SimpleGraph.card_neighborFinset_eq_degree]
            apply Finset.card_le_card_of_injOn f
            · intro w hw
              rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hw ⊢
              exact f.map_adj_iff.2 hw
            · intro w _ w' _ h
              exact f.injective h
        _ ≤ 2 := path_graph_degree_le_two _ _
    have hpos : ∀ v, 0 < G.degree v := simple_graph_connected_degree_pos G hT.1 hk
    have hz : (∑ v, ((G.degree v).choose 2 : ℤ)) ≤ ∑ v, ((G.degree v : ℤ) - 1) := by
      apply Finset.sum_le_sum
      intro v _
      have h1 := hdeg2 v
      have h2 := hpos v
      generalize G.degree v = d at h1 h2
      interval_cases d <;> simp
    have hlow := (simple_graph_is_tree_card_sub_two_le_sum_choose_degree_le_choose G hT hk).1
    rw [hsub1] at hz
    have : ((∑ v, (G.degree v).choose 2 : ℕ) : ℤ) ≤ ((Fintype.card V - 2 : ℕ) : ℤ) := by
      push_cast
      rw [Nat.cast_sub hk]
      push_cast
      exact hz
    have := Int.ofNat_le.1 this
    omega
