import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphSafe17Graph
import AFTD.Kb.Tcs.DigraphDirectedCycleOn
import AFTD.Kb.Tcs.DigraphSafe17Structure

/-!
# digraph_safe17_two_cycle_impossible

Topic: graphs   Node: 55c17a8243a1

Provenance: helper lemma. Safe-cycle obstruction for OP-110; experiment 13260.

The displayed oriented graph has no directed cycle on two vertices.
-/

private instance in504_safe17_final_decAdj_3 : DecidableRel digraph_safe17_graph.Adj := by
  intro u v
  unfold digraph_safe17_graph
  infer_instance

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem digraph_safe17_two_cycle_impossible
    (C : Finset (Fin 17)) (hcycle : digraph_directed_cycle_on digraph_safe17_graph C)
    (hcard : C.card = 2) : False := by
  obtain ⟨l,hn,hlen0,hset,hchain,hclose⟩ := hcycle
  have hlen : l.length = 2 := by
    have h := List.toFinset_card_of_nodup hn
    rw [hset,hcard] at h
    omega
  have hshape : ∃ u a, l = [u,a] := by
    cases l with
    | nil => simp at hlen
    | cons u l =>
      cases l with
      | nil => simp at hlen
      | cons a l =>
        cases l with
        | nil => exact ⟨u,a,rfl⟩
        | cons b l => simp at hlen
  obtain ⟨u,a,rfl⟩ := hshape
  have hua : digraph_safe17_graph.Adj u a := by simpa [List.isChain_cons_cons] using hchain
  have hau : digraph_safe17_graph.Adj a u := by
    obtain ⟨x,y,hx,hy,hxy⟩ := hclose
    simp only [List.head?_cons, Option.some.injEq] at hx
    simp at hy
    subst x
    subst y
    exact hxy
  exact (digraph_safe17_structure.2.1 u a hua) hau
