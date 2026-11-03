import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphSafe17Graph

/-!
# digraph_safe17_three_neighbors_not_safe

Topic: graphs   Node: 6adf1d529794

Provenance: helper lemma. Safe-cycle obstruction for OP-110; experiment 13260.

An outside vertex pointing to three distinct vertices in a set violates the displayed two-neighbor safety condition.
-/

private instance in504_safe17_final_decAdj_1 : DecidableRel digraph_safe17_graph.Adj := by
  intro u v
  unfold digraph_safe17_graph
  infer_instance

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem digraph_safe17_three_neighbors_not_safe
    (C : Finset (Fin 17)) (v p q r : Fin 17)
    (hv : v ∉ C) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hp : p ∈ C) (hq : q ∈ C) (hr : r ∈ C)
    (hvp : digraph_safe17_graph.Adj v p) (hvq : digraph_safe17_graph.Adj v q)
    (hvr : digraph_safe17_graph.Adj v r)
    (hsafe : ∀ x ∉ C, (C.filter fun w => digraph_safe17_graph.Adj x w).card ≤ 2) : False := by
  classical
  have hsub : ({p,q,r} : Finset (Fin 17)) ⊆ C.filter fun w => digraph_safe17_graph.Adj v w := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨hp,hvp⟩
    · exact Finset.mem_filter.mpr ⟨hq,hvq⟩
    · exact Finset.mem_filter.mpr ⟨hr,hvr⟩
  have hcard : ({p,q,r} : Finset (Fin 17)).card = 3 := by simp [hpq,hpr,hqr]
  have hc := Finset.card_le_card hsub
  have hb := hsafe v hv
  omega
