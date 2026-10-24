import AFTD.Prelude
import AFTD.Kb.Tcs.AdditiveColoringBoundByDegree

/-!
# additive_coloring_bipartite_maxDegree_add_one

Topic: graphs   Node: c5100cb0ab3b

Provenance: formalization of a published result. Source: arXiv:2610.30174: Theorem 2.1

Every finite connected bipartite graph with maximum degree at least 2 admits an additive coloring f with 1 ≤ f(v) ≤ Delta(G) + 1 for all vertices v.
-/

/-- Every finite connected bipartite graph with maximum degree at least 2 admits an additive coloring with labels at most its maximum degree plus 1. -/
theorem additive_coloring_bipartite_maxDegree_add_one
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (_hconn : G.Connected) (_hbip : G.IsBipartite) (_hdeg : 2 ≤ G.maxDegree) :
    ∃ f : V → ℕ, (∀ v, 1 ≤ f v ∧ f v ≤ G.maxDegree + 1) ∧
      ∀ ⦃u v : V⦄, G.Adj u v →
        ∑ w ∈ G.neighborFinset u, f w ≠ ∑ w ∈ G.neighborFinset v, f w := by
  obtain ⟨f, -, hf_adj, hf_bound⟩ :=
    additive_coloring_bound_by_degree G (fun _ => 1) (fun _ => Nat.one_pos)
  refine ⟨f, fun v => ⟨(hf_bound v).1, ?_⟩, hf_adj⟩
  have := (hf_bound v).2
  have hdeg_le : G.degree v ≤ G.maxDegree := G.degree_le_maxDegree v
  omega
