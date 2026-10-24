import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphEdgeCount
import AFTD.Kb.Tcs.DigraphEdgeCountEqSumOutdegrees

/-!
# digraph_outdegree_three_mul_le_edge_count

Topic: graphs   Node: de7037a656cb

Provenance: helper lemma. Helper for digraph_both_cuts_ge_ceil_div_six_of_indegree_lt, arXiv:2610.21381, proof of Theorem 1.4, Case 2. The two-partition certificate and paired-outcome inequality are a deterministic formulation of the paper's averaging argument; no research advance is claimed.

In a finite loopless digraph of minimum outdegree at least two, three times any vertex outdegree is at most the total number of arcs.
-/

theorem digraph_outdegree_three_mul_le_edge_count {V : Type*} [Fintype V]
    [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
    (hloop : ∀ v, ¬ G.Adj v v)
    (hdeg : ∀ v, 2 ≤ (Finset.univ.filter (G.Adj v)).card) (v : V) :
    3 * (Finset.univ.filter (G.Adj v)).card ≤ digraph_edge_count G := by
  let d : V → ℕ := fun u => (Finset.univ.filter (G.Adj u)).card
  have hd : d v ≤ (Finset.univ.erase v).card := by
    apply Finset.card_le_card
    intro u hu
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_univ u⟩
    intro h
    subst u
    exact hloop v (Finset.mem_filter.mp hu).2
  have hother : (Finset.univ.erase v).card * 2 ≤ ∑ u ∈ Finset.univ.erase v, d u := by
    calc
      _ = ∑ _u ∈ Finset.univ.erase v, 2 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun u _ => hdeg u)
  have hsplit : (∑ u ∈ Finset.univ.erase v, d u) + d v = digraph_edge_count G := by
    rw [Finset.sum_erase_add _ _ (Finset.mem_univ v)]
    exact (digraph_edge_count_eq_sum_outdegrees G).symm
  change 3 * d v ≤ digraph_edge_count G
  omega
