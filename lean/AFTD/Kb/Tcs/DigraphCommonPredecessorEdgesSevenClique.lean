import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphCommonPredecessorGraph

/-!
# digraph_common_predecessor_edges_seven_clique

Topic: graphs   Node: bac7d09d5396

Provenance: helper lemma. Out-neighborhood clique structure for the minimum-counterexample route to OP-110.

In a 7-outregular finite digraph, every edge of its common-predecessor graph lies in a clique of exactly seven vertices.
-/

theorem digraph_common_predecessor_edges_seven_clique
    (α : Type) [Fintype α] [DecidableEq α]
    (D : Digraph α) [DecidableRel D.Adj]
    (hreg : ∀ v, (Finset.univ.filter fun w => D.Adj v w).card = 7) :
    ∀ u v, (digraph_common_predecessor_graph D).Adj u v →
      ∃ S : Finset α, S.card = 7 ∧ u ∈ S ∧ v ∈ S ∧
        (digraph_common_predecessor_graph D).IsClique (S : Set α) := by
  intro u v huv
  obtain ⟨hne, w, hwu, hwv⟩ := huv
  let S : Finset α := Finset.univ.filter fun x => D.Adj w x
  refine ⟨S, hreg w, ?_, ?_, ?_⟩
  · simp [S, hwu]
  · simp [S, hwv]
  · intro x hx y hy hxy
    have hwx : D.Adj w x := (Finset.mem_filter.mp hx).2
    have hwy : D.Adj w y := (Finset.mem_filter.mp hy).2
    exact ⟨hxy, w, hwx, hwy⟩
