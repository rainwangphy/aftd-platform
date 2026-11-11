import AFTD.Prelude
import AFTD.Kb.Tcs.TenVertexExchangeGraph
import AFTD.Kb.Tcs.TenVertexExchangeEdges
import AFTD.Kb.Tcs.TenVertexExchangeFamilyEq
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# ten_vertex_exchange_six_connected

Topic: graphs   Node: 7ddeab4a9a1f

Provenance: helper lemma. Explicit ten-vertex witness for simple_graph_stable_point_irreducible_forced_exchange_barrier_counterexample.

Deleting any at most five vertices leaves the ten-vertex witness graph connected.
-/

open scoped Sym2
open SimpleGraph

def tv_adj (u v : Fin 10) : Prop := s(u,v) ∈ ten_vertex_exchange_edges ∧ u ≠ v
instance (u v : Fin 10) : Decidable (tv_adj u v) := by unfold tv_adj; infer_instance
lemma tv_adj_iff (u v : Fin 10) : tv_adj u v ↔ ten_vertex_exchange_graph.Adj u v := by
  simp [tv_adj, ten_vertex_exchange_graph, SimpleGraph.fromEdgeSet_adj]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
lemma tv_min_degree : ∀ u : Fin 10, 6 ≤ ((Finset.univ : Finset (Fin 10)).filter (tv_adj u)).card := by
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
lemma tv_no_four_cycle_complement : ∀ (a b c d : Fin 10),
    a ≠ b → c ≠ d → c ≠ a → c ≠ b → d ≠ a → d ≠ b →
    ¬ tv_adj a c → ¬ tv_adj b c → ¬ tv_adj a d → ¬ tv_adj b d → False := by
  decide


lemma tv_neighbor_survives (R : Finset (Fin 10)) (hR : R.card ≤ 5)
    (u : Fin 10) : ∃ v, v ∉ R ∧ tv_adj u v := by
  let N := (Finset.univ : Finset (Fin 10)).filter (tv_adj u)
  have hN : 6 ≤ N.card := tv_min_degree u
  have hns : ¬ N ⊆ R := by
    intro h
    have := Finset.card_le_card h
    omega
  obtain ⟨v, hvN, hvR⟩ := Finset.not_subset.mp hns
  exact ⟨v, hvR, (Finset.mem_filter.mp hvN).2⟩

lemma tv_survivor (R : Finset (Fin 10)) (hR : R.card ≤ 5) : ∃ u : Fin 10, u ∉ R := by
  have h : ¬ (Finset.univ : Finset (Fin 10)) ⊆ R := by
    intro h
    have hc := Finset.card_le_card h
    simp only [Finset.card_univ, Fintype.card_fin] at hc
    omega
  obtain ⟨u, _, hu⟩ := Finset.not_subset.mp h
  exact ⟨u, hu⟩

theorem ten_vertex_exchange_six_connected : ∀ R : Finset (Fin 10), R.card ≤ 5 → (ten_vertex_exchange_graph.induce {v | v ∉ R}).Connected := by
  intro R hR
  let K := ten_vertex_exchange_graph.induce {v | v ∉ R}
  have hn : ∀ u : {v // v ∉ R}, ∃ v, K.Adj u v := by
    intro u
    obtain ⟨v, hv, huv⟩ := tv_neighbor_survives R hR u.val
    exact ⟨⟨v, hv⟩, (tv_adj_iff u.val v).mp huv⟩
  apply (SimpleGraph.connected_iff K).mpr
  constructor
  · intro a b
    by_contra hnot
    obtain ⟨x, hax⟩ := hn a
    obtain ⟨y, hby⟩ := hn b
    have cross {u v : {v // v ∉ R}} (hu : K.Reachable a u) (hv : K.Reachable b v) :
        u ≠ v ∧ ¬ K.Adj u v := by
      constructor
      · intro he
        subst v
        exact hnot (hu.trans hv.symm)
      · intro h
        exact hnot ((hu.trans h.reachable).trans hv.symm)
    have h1 := cross (SimpleGraph.Reachable.refl a) (SimpleGraph.Reachable.refl b)
    have h2 := cross hax.reachable (SimpleGraph.Reachable.refl b)
    have h3 := cross (SimpleGraph.Reachable.refl a) hby.reachable
    have h4 := cross hax.reachable hby.reachable
    have hnval {u v : {v // v ∉ R}} (h : u ≠ v) : u.val ≠ v.val := by
      intro he
      apply h
      exact Subtype.ext he
    have hnadj {u v : {v // v ∉ R}} (h : ¬ K.Adj u v) : ¬ tv_adj u.val v.val := by
      intro h'
      apply h
      exact (tv_adj_iff u.val v.val).mp h'
    exact tv_no_four_cycle_complement a.val x.val b.val y.val
      (hnval hax.ne) (hnval hby.ne) (hnval h1.1).symm (hnval h2.1).symm
      (hnval h3.1).symm (hnval h4.1).symm (hnadj h1.2) (hnadj h2.2) (hnadj h3.2) (hnadj h4.2)
  · obtain ⟨u, hu⟩ := tv_survivor R hR
    exact ⟨⟨u, hu⟩⟩
