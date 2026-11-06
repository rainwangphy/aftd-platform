import AFTD.Prelude
import AFTD.Kb.Tcs.StochasticMstPriorityCost
import AFTD.Kb.Tcs.StochasticMstAdaptiveCost
import AFTD.Kb.Tcs.StochasticMstPriorityCostAux
import AFTD.Kb.Tcs.StochasticMstQueryEligible
import AFTD.Kb.Tcs.StochasticMstAdaptiveCostAux

/-!
# stochastic_mst_adaptive_cost_le_priority_cost

Topic: algorithms   Node: 6a35ad218ceb

Provenance: helper lemma. The easy inequality behind OP-1209 (arXiv:2610.40844 (Stochastic Minimum Spanning Tree Identification with Binary Weights), Sec. 3): fixed-priority strategies are among the adaptive ones

For every finite simple graph G and every p with 0 <= p_e <= 1 on the edges, A(G,p) <= P(G,p): every fixed-priority strategy is an adaptive Tutte strategy, so the optimal adaptive cost is at most its cost.
-/

theorem stochastic_mst_adaptive_cost_aux_le_priority_cost_aux {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p : Sym2 V → ℝ)
    (hp : ∀ e ∈ G.edgeSet, 0 ≤ p e ∧ p e ≤ 1) (π : List (Sym2 V))
    (hπ : ∀ e ∈ G.edgeFinset, e ∈ π) (k : ℕ) :
    ∀ Z D, stochastic_mst_adaptive_cost_aux G p k Z D ≤
      stochastic_mst_priority_cost_aux G p π k Z D := by
  induction k with
  | zero => intro Z D; exact le_refl _
  | succ k ih =>
    intro Z D
    classical
    simp only [stochastic_mst_adaptive_cost_aux, stochastic_mst_priority_cost_aux]
    have key : ∀ e, List.find? (fun e => decide (stochastic_mst_query_eligible G Z D e)) π = some e →
        e ∈ G.edgeFinset.filter (fun e => stochastic_mst_query_eligible G Z D e) ∧
          stochastic_mst_query_eligible G Z D e := by
      intro e h
      have he := List.find?_some h
      simp only [decide_eq_true_eq] at he
      exact ⟨Finset.mem_filter.mpr ⟨(SimpleGraph.mem_edgeFinset).mpr he.1, he⟩, he⟩
    split
    · rename_i hne
      split
      · rename_i h
        exfalso
        obtain ⟨e, he⟩ := hne
        rw [Finset.mem_filter] at he
        rw [List.find?_eq_none] at h
        have := h e (hπ e he.1)
        simp only [decide_eq_true_eq] at this
        exact this he.2
      · rename_i e h
        obtain ⟨hmem, he⟩ := key e h
        refine le_trans (Finset.inf'_le _ hmem) ?_
        have h1 := hp e he.1
        have h2 := mul_le_mul_of_nonneg_left (ih Z (insert e D)) h1.1
        have h3 := mul_le_mul_of_nonneg_left (ih (insert e Z) D) (sub_nonneg.mpr h1.2)
        try simp only
        linarith
    · rename_i hne
      split
      · exact le_refl _
      · rename_i e h
        exact absurd ⟨e, (key e h).1⟩ hne

theorem stochastic_mst_adaptive_cost_le_priority_cost {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p : Sym2 V → ℝ)
    (hp : ∀ e ∈ G.edgeSet, 0 ≤ p e ∧ p e ≤ 1) :
    stochastic_mst_adaptive_cost G p ≤ stochastic_mst_priority_cost G p := by
  unfold stochastic_mst_priority_cost
  refine le_csInf ⟨_, G.edgeFinset.toList, List.Perm.refl _, rfl⟩ ?_
  rintro x ⟨π, hπ, rfl⟩
  exact stochastic_mst_adaptive_cost_aux_le_priority_cost_aux G p hp π
    (fun e he => hπ.mem_iff.mpr (Finset.mem_toList.mpr he)) _ ∅ ∅
