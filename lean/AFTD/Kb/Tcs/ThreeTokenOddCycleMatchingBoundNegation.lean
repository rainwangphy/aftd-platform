import AFTD.Prelude
import AFTD.Kb.Tcs.TokenGraph

/-!
# three_token_odd_cycle_matching_bound_negation

Topic: graphs   Node: 6c1130b25773

Provenance: formalization of a published result. Source: arXiv:2611.22830 Section 5 -- Independent sets in the 2-token graph of a cycle and kings on the torus

It is not the case that for all integers k ≥ 2, the independence number of the 3-token graph of the odd cycle C_{2k+1} is equal to ((2 * k + 1).choose 3 + k) / 2.
-/

instance three_token_odd_cycle_matching_bound_negation_cycleGraph_decidableRel (n : ℕ) :
    DecidableRel (SimpleGraph.cycleGraph n).Adj := by
  intro a b
  dsimp [SimpleGraph.cycleGraph]
  split <;> infer_instance

instance three_token_odd_cycle_matching_bound_negation_token_graph_decidableRel
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    DecidableRel (token_graph G k).Adj := by
  intro ⟨x, hx⟩ ⟨y, hy⟩
  dsimp [token_graph]
  infer_instance

abbrev three_token_odd_cycle_matching_bound_negation_G5 :
    SimpleGraph {s : Finset (Fin 5) // s.card = 3} :=
  token_graph (SimpleGraph.cycleGraph 5) 3

lemma three_token_odd_cycle_matching_bound_negation_isIndepSet_iff
    (s : Finset {s : Finset (Fin 5) // s.card = 3}) :
    three_token_odd_cycle_matching_bound_negation_G5.IsIndepSet (s : Set _) ↔
      ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ¬ three_token_odd_cycle_matching_bound_negation_G5.Adj x y := by
  dsimp [SimpleGraph.IsIndepSet, Set.Pairwise]
  simp only [Finset.mem_coe]

instance three_token_odd_cycle_matching_bound_negation_isIndepSet_decidable
    (s : Finset {s : Finset (Fin 5) // s.card = 3}) :
    Decidable (three_token_odd_cycle_matching_bound_negation_G5.IsIndepSet (s : Set _)) :=
  decidable_of_iff (∀ x ∈ s, ∀ y ∈ s, x ≠ y → ¬ three_token_odd_cycle_matching_bound_negation_G5.Adj x y)
    (three_token_odd_cycle_matching_bound_negation_isIndepSet_iff s).symm

set_option maxRecDepth 500000 in
theorem three_token_odd_cycle_matching_bound_negation_no_indep_6 :
    ¬ ∃ s : Finset {s : Finset (Fin 5) // s.card = 3},
      s.card = 6 ∧ three_token_odd_cycle_matching_bound_negation_G5.IsIndepSet (s : Set _) := by
  decide

/-- The matching upper bound is not sharp for the 3-token graph of every odd cycle C_{2k+1}. -/
theorem three_token_odd_cycle_matching_bound_negation :
    ¬ (∀ k ≥ 2, (token_graph (SimpleGraph.cycleGraph (2 * k + 1)) 3).indepNum = ((2 * k + 1).choose 3 + k) / 2) := by
  intro h
  have h2 := h 2 (by omega)
  have h_val : ((2 * 2 + 1).choose 3 + 2) / 2 = 6 := by rfl
  have h_indep : (token_graph (SimpleGraph.cycleGraph 5) 3).indepNum = 6 := by
    have h_cg : 2 * 2 + 1 = 5 := by rfl
    rw [h_cg] at h2
    rw [h_val] at h2
    exact h2
  obtain ⟨s, hs⟩ := SimpleGraph.exists_isNIndepSet_indepNum (G := three_token_odd_cycle_matching_bound_negation_G5)
  rw [h_indep] at hs
  rw [SimpleGraph.isNIndepSet_iff] at hs
  exact three_token_odd_cycle_matching_bound_negation_no_indep_6 ⟨s, hs.2, hs.1⟩
