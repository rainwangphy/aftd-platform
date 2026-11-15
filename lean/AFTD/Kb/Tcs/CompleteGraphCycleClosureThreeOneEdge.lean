import AFTD.Prelude
import AFTD.Kb.Tcs.CompleteGraphCycleClosure

/-!
# complete_graph_cycle_closure_three_one_edge

Topic: graphs   Node: 914ed10f9e0b

Provenance: helper lemma. sanity lemma for complete_graph_cycle_closure

In the cycle matroid of K_3, a single edge is closed.
-/

lemma complete_graph_cycle_closure_three_one_edge_walk_subset {V : Type*} {u v : V} {a b : V}
    (w : (SimpleGraph.fromEdgeSet {s(u, v)}).Walk a b) :
    a = b ∨ (a ∈ ({u, v} : Set V) ∧ b ∈ ({u, v} : Set V)) := by
  induction w with
  | nil => left; rfl
  | @cons x y z h_adj w_tail ih =>
    rw [SimpleGraph.fromEdgeSet_adj] at h_adj
    rcases h_adj with ⟨h_mem, h_ne⟩
    rw [Set.mem_singleton_iff, Sym2.eq_iff] at h_mem
    right
    have hy : y ∈ ({u, v} : Set V) := by
      rcases h_mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · right; rfl
      · left; rfl
    have hx : x ∈ ({u, v} : Set V) := by
      rcases h_mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · left; rfl
      · right; rfl
    refine ⟨hx, ?_⟩
    rcases ih with rfl | ⟨-, hz⟩
    · exact hy
    · exact hz

lemma complete_graph_cycle_closure_three_one_edge_reachable_eq {V : Type*} {u v : V} {a b : V} (hab : a ≠ b)
    (h : (SimpleGraph.fromEdgeSet {s(u, v)}).Reachable a b) :
    s(a, b) = s(u, v) := by
  obtain ⟨w⟩ := h
  have hw := complete_graph_cycle_closure_three_one_edge_walk_subset w
  rcases hw with rfl | ⟨ha, hb⟩
  · exact False.elim (hab rfl)
  · rw [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rw [Sym2.eq_iff]
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact False.elim (hab rfl)
    · left; exact ⟨rfl, rfl⟩
    · right; exact ⟨rfl, rfl⟩
    · exact False.elim (hab rfl)

theorem complete_graph_cycle_closure_three_one_edge (e : (⊤ : SimpleGraph (Fin 3)).edgeSet) :
    complete_graph_cycle_closure 3 {e} = {e} := by
  obtain ⟨u, v, he⟩ : ∃ u v, e.val = s(u, v) := by
    induction e.val using Sym2.inductionOn with
    | hf u v => exact ⟨u, v, rfl⟩
  have he_ne : u ≠ v := by
    have he_prop := e.prop
    rw [he] at he_prop
    simp only [SimpleGraph.edgeSet_top, Set.mem_compl_iff, Sym2.mem_diagSet, Sym2.mk_isDiag_iff] at he_prop
    exact he_prop
  ext x
  simp only [complete_graph_cycle_closure, Set.mem_ofPred_eq, Set.image_singleton, Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, b, hx_eq, h_reach⟩
    have hx_prop := x.prop
    rw [hx_eq] at hx_prop
    simp only [SimpleGraph.edgeSet_top, Set.mem_compl_iff, Sym2.mem_diagSet, Sym2.mk_isDiag_iff] at hx_prop
    rw [he] at h_reach
    have h_sab := complete_graph_cycle_closure_three_one_edge_reachable_eq hx_prop h_reach
    apply Subtype.ext
    rw [hx_eq, he, h_sab]
  · rintro rfl
    refine ⟨u, v, he, ?_⟩
    rw [he]
    have h_adj : (SimpleGraph.fromEdgeSet {s(u, v)}).Adj u v := by
      rw [SimpleGraph.fromEdgeSet_adj]
      exact ⟨Set.mem_singleton _, he_ne⟩
    exact h_adj.reachable
