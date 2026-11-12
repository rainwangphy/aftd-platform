import AFTD.Prelude
import AFTD.Kb.Tcs.GtsGraph

/-!
# op223_nonleaf_count_counterexample

Topic: graphs   Node: 578ed15c1f8e

Provenance: original. Related work: arXiv:2610.17078 Open Problem 6.1; counterexample to an auxiliary statement

There is a graph on three vertices with adjacent u and v of degree at least two for which the adjacent shift reduces the number of vertices of degree greater than one by more than one.
-/

open SimpleGraph
open scoped Classical

def op223_triangle : SimpleGraph (Fin 3) := ⊤
def op223_triangle_shift : SimpleGraph (Fin 3) := gts_graph op223_triangle 0 1 0

theorem op223_triangle_shift_graph :
    op223_triangle_shift = SimpleGraph.fromEdgeSet {s(0,1), s(0,2)} := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp only [op223_triangle_shift, op223_triangle, gts_graph, SimpleGraph.sup_adj,
      SimpleGraph.deleteEdges_adj, SimpleGraph.fromEdgeSet_adj, Set.mem_setOf_eq,
      Set.mem_insert_iff, Set.mem_singleton_iff, SimpleGraph.top_adj, Sym2.eq,
      Fin.exists_fin_succ] <;> decide

lemma op223_triangle_neighbors (x : Fin 3) :
    op223_triangle.neighborSet x = ((Finset.univ.erase x : Finset (Fin 3)) : Set (Fin 3)) := by
  ext y
  simp [op223_triangle, SimpleGraph.neighborSet, SimpleGraph.top_adj, ne_comm]

lemma op223_triangle_degree (x : Fin 3) : Nat.card (op223_triangle.neighborSet x) = 2 := by
  rw [Nat.card_coe_set_eq, op223_triangle_neighbors, Set.ncard_coe_finset]
  simp

lemma op223_triangle_shift_degree_zero : Nat.card (op223_triangle_shift.neighborSet 0) = 2 := by
  have h : op223_triangle_shift.neighborSet 0 = (({1,2} : Finset (Fin 3)) : Set (Fin 3)) := by
    rw [op223_triangle_shift_graph]
    ext x; fin_cases x <;> simp only [SimpleGraph.mem_neighborSet, SimpleGraph.fromEdgeSet_adj,
      Set.mem_insert_iff, Set.mem_singleton_iff, Sym2.eq, Finset.mem_coe, Finset.mem_insert,
      Finset.mem_singleton] <;> decide
  rw [Nat.card_coe_set_eq,h,Set.ncard_coe_finset]
  norm_num [Finset.card_insert_eq_ite, Fin.ext_iff]

lemma op223_triangle_shift_degree_one : Nat.card (op223_triangle_shift.neighborSet 1) = 1 := by
  have h : op223_triangle_shift.neighborSet 1 = (({0} : Finset (Fin 3)) : Set (Fin 3)) := by
    rw [op223_triangle_shift_graph]
    ext x; fin_cases x <;> simp only [SimpleGraph.mem_neighborSet, SimpleGraph.fromEdgeSet_adj,
      Set.mem_insert_iff, Set.mem_singleton_iff, Sym2.eq, Finset.mem_coe, Finset.mem_insert,
      Finset.mem_singleton] <;> decide
  rw [Nat.card_coe_set_eq,h,Set.ncard_coe_finset]
  norm_num

lemma op223_triangle_shift_degree_two : Nat.card (op223_triangle_shift.neighborSet 2) = 1 := by
  have h : op223_triangle_shift.neighborSet 2 = (({0} : Finset (Fin 3)) : Set (Fin 3)) := by
    rw [op223_triangle_shift_graph]
    ext x; fin_cases x <;> simp only [SimpleGraph.mem_neighborSet, SimpleGraph.fromEdgeSet_adj,
      Set.mem_insert_iff, Set.mem_singleton_iff, Sym2.eq, Finset.mem_coe, Finset.mem_insert,
      Finset.mem_singleton] <;> decide
  rw [Nat.card_coe_set_eq,h,Set.ncard_coe_finset]
  norm_num

theorem op223_nonleaf_count_counterexample :
    ∃ (T : SimpleGraph (Fin 3)) (u v : Fin 3), T.Adj u v ∧
      2 ≤ Nat.card (T.neighborSet u) ∧ 2 ≤ Nat.card (T.neighborSet v) ∧
      (Finset.univ.filter (fun x : Fin 3 => 1 < Nat.card ((gts_graph T u v u).neighborSet x))).card + 1 <
        (Finset.univ.filter (fun x : Fin 3 => 1 < Nat.card (T.neighborSet x))).card := by
  refine ⟨op223_triangle, 0, 1, ?_, ?_, ?_, ?_⟩
  · simp [op223_triangle]
  · rw [op223_triangle_degree]
  · rw [op223_triangle_degree]
  · change (Finset.univ.filter (fun x : Fin 3 => 1 < Nat.card (op223_triangle_shift.neighborSet x))).card + 1 <
        (Finset.univ.filter (fun x : Fin 3 => 1 < Nat.card (op223_triangle.neighborSet x))).card
    have hf : Finset.univ.filter (fun x : Fin 3 => 1 < Nat.card (op223_triangle_shift.neighborSet x)) = {0} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      fin_cases x
      · change (1 < Nat.card (op223_triangle_shift.neighborSet 0)) ↔ (0 : Fin 3) = 0
        rw [op223_triangle_shift_degree_zero]; decide
      · change (1 < Nat.card (op223_triangle_shift.neighborSet 1)) ↔ (1 : Fin 3) = 0
        rw [op223_triangle_shift_degree_one]; decide
      · change (1 < Nat.card (op223_triangle_shift.neighborSet 2)) ↔ (2 : Fin 3) = 0
        rw [op223_triangle_shift_degree_two]; decide
    have hg : Finset.univ.filter (fun x : Fin 3 => 1 < Nat.card (op223_triangle.neighborSet x)) = Finset.univ := by
      apply Finset.filter_true_of_mem
      intro x hx
      rw [op223_triangle_degree]
      decide
    rw [hf, hg]
    simp
