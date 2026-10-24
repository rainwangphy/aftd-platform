import AFTD.Prelude
import AFTD.Kb.Tcs.IsAdditiveColoring
import AFTD.Kb.Tcs.SimpleGraphExistsEdgeTailCapacity
import AFTD.Kb.Tcs.SimpleGraphBipartiteAdditiveListsOfEdgeAssignment

/-!
# op_494_additive_chromatic_bipartite_maxDegree

Topic: graphs   Node: fd4a2809ece6

Provenance: formalization of a published result. Source: Known consequence of arXiv:2302.02190v3, Corollary 5.3, and the standard incidence matching construction of an orientation with outdegree at most maximum-degree-minus-one when the maximum degree is at least two. Formalizes OP-494 in arXiv:2610.30174; this is a literature consequence, not a new research result.

Let G be a finite connected bipartite simple graph with maximum degree at least 2. Then there exists a vertex labeling f : V → ℕ such that 1 ≤ f(v) ≤ G.maxDegree for all v, and adjacent vertices have different neighborhood sums ∑_{w ∈ N(u)} f(w) ≠ ∑_{w ∈ N(v)} f(w).
-/

open scoped BigOperators

/-- Open Problem OP-494: every connected bipartite finite simple graph with maximum degree at least 2 admits an additive coloring with labels at most its maximum degree. -/
theorem op_494_additive_chromatic_bipartite_maxDegree
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hbip : G.IsBipartite) (hdeg : 2 ≤ G.maxDegree) :
    ∃ f : V → ℕ, (∀ v, 1 ≤ f v ∧ f v ≤ G.maxDegree) ∧
      ∀ ⦃u v : V⦄, G.Adj u v →
        ∑ w ∈ G.neighborFinset u, f w ≠ ∑ w ∈ G.neighborFinset v, f w := by
  classical
  obtain ⟨tail, htail, hcap⟩ := simple_graph_exists_edge_tail_capacity G hdeg
  obtain ⟨f, hf, hadd⟩ := simple_graph_bipartite_additive_lists_of_edge_assignment
    G hbip tail htail (fun _ => Finset.Icc 1 G.maxDegree) (by
      intro v
      have hc := hcap v
      simp only [Nat.card_Icc]
      omega)
  exact ⟨f, fun v => Finset.mem_Icc.mp (hf v), hadd⟩
