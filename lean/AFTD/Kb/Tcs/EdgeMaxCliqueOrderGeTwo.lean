import AFTD.Prelude
import AFTD.Kb.Tcs.EdgeMaxCliqueOrder

/-!
# edge_max_clique_order_ge_two

Topic: graphs   Node: efa5633314b7

Provenance: helper lemma. scout/2611-30029-an-exact-vertex-localization-of-zykov-s-theorem.md:211

For every edge e in the edge finset of a finite simple graph G, the maximum order of a clique containing e is at least two.
-/

lemma edge_max_clique_order_ge_two_of_mem_edgeSet {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {e : Sym2 V} (he : e ∈ G.edgeSet) :
    2 ≤ edge_max_clique_order G e := by
  have hclique : G.IsClique (e.toFinset : Set V) := by
    induction e using Sym2.inductionOn
    rename_i u v
    rw [Sym2.toFinset_mk_eq, Finset.coe_pair, SimpleGraph.isClique_pair]
    intro _
    exact he
  have hcard : e.toFinset.card = 2 := by
    have hdiag : ¬ e.IsDiag := G.not_isDiag_of_mem_edgeSet he
    exact Sym2.card_toFinset_of_not_isDiag e hdiag
  rw [← hcard]
  unfold edge_max_clique_order
  classical
  refine Finset.le_sup (f := Finset.card) ?_
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, hclique, subset_rfl⟩

/-- Every edge of a graph is contained in a clique of size at least two. -/
theorem edge_max_clique_order_ge_two {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {e : Sym2 V} (he : e ∈ G.edgeFinset) :
    2 ≤ edge_max_clique_order G e := edge_max_clique_order_ge_two_of_mem_edgeSet G (SimpleGraph.mem_edgeFinset.mp he)
