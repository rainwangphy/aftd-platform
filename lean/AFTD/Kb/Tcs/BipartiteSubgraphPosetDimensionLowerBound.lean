import AFTD.Prelude
import AFTD.Kb.Tcs.BipartitePosetLe
import AFTD.Kb.Tcs.PosetDimension
import AFTD.Kb.Tcs.BipartiteSubgraphPosetDimensionPowLowerBound

/-!
# bipartite_subgraph_poset_dimension_lower_bound

Topic: combinatorics   Node: 1e320fe05b19

Provenance: formalization of a published result. Source: arXiv:2610.24774 Section 4.1, Lemma 4.2

Let V be a finite type with decidable equality, G a simple graph on V with decidable adjacency, and A, B subsets of V covering V such that G is bipartite with parts A and B. Let N = Fintype.card V and M = G.edgeFinset.card, with 2 ≤ N. Then there exists a spanning subgraph H ≤ G such that (M : ℝ) / Real.logb 2 (N.factorial : ℝ) ≤ (poset_dimension (bipartite_poset_le H A B) : ℝ).
-/

/-- Dimension lower bound for subgraphs of a bipartite graph (arXiv:2610.24774 Lemma 4.2). -/
theorem bipartite_subgraph_poset_dimension_lower_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Set V) (h_cov : A ∪ B = Set.univ) (h_bip : G.IsBipartiteWith A B)
    (N M : ℕ) (hN : Fintype.card V = N) (hM : G.edgeFinset.card = M)
    (hN2 : 2 ≤ N) :
    ∃ H : SimpleGraph V, H ≤ G ∧
      (M : ℝ) / Real.logb 2 (N.factorial : ℝ) ≤ (poset_dimension (bipartite_poset_le H A B) : ℝ) := by
  obtain ⟨H, hHG, hineq⟩ :=
    bipartite_subgraph_poset_dimension_pow_lower_bound G A B h_cov h_bip N M hN hM hN2
  refine ⟨H, hHG, ?_⟩
  set d : ℕ := poset_dimension (bipartite_poset_le H A B) with hd
  have hineq' : 2 ^ M ≤ N.factorial ^ d := by
    rw [hd]; exact hineq
  have hineqR : (2 : ℝ) ^ M ≤ (N.factorial : ℝ) ^ d := by
    exact_mod_cast hineq'
  have hx1 : (1 : ℝ) < (N.factorial : ℝ) := by
    have h : 1 < N.factorial := Nat.one_lt_factorial.mpr (by omega)
    exact_mod_cast h
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : (M : ℝ) * Real.log 2 ≤ (d : ℝ) * Real.log (N.factorial : ℝ) := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ M) hineqR
    simpa only [Real.log_pow] using h
  have hMle : (M : ℝ) ≤ (d : ℝ) * Real.logb 2 (N.factorial : ℝ) := by
    rw [Real.logb]
    rw [← mul_div_assoc]
    exact (le_div_iff₀ hlog2).mpr hlog
  have hLpos : 0 < Real.logb 2 (N.factorial : ℝ) :=
    Real.logb_pos (by norm_num) hx1
  exact (div_le_iff₀ hLpos).mpr hMle
