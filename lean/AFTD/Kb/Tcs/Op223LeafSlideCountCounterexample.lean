import AFTD.Prelude

/-!
# op223_leaf_slide_count_counterexample

Topic: graphs   Node: bc3b48f3e625

Provenance: original. Related work: arXiv:2610.17078 Open Problem 6.1; counterexample to an auxiliary statement

There is a graph on exactly four vertices with vertices u, v and b, where u and v are distinct, b is distinct from v, v has exactly one neighbor, u-b is an edge and v-b is not, for which replacing u-b by v-b reduces the number of vertices of degree one by more than one.
-/

open SimpleGraph
open scoped Classical

def op223_leaf_example : SimpleGraph (Fin 4) := SimpleGraph.pathGraph 4
def op223_leaf_example_after : SimpleGraph (Fin 4) :=
  op223_leaf_example.deleteEdges {s(0,1)} ⊔ SimpleGraph.fromEdgeSet {s(3,1)}

lemma op223_leaf_example_degree_0 : Nat.card (op223_leaf_example.neighborSet 0) = 1 := by
  have h : op223_leaf_example.neighborSet 0 = (({1} : Finset (Fin 4)) : Set (Fin 4)) := by
    ext x
    fin_cases x <;> simp only [SimpleGraph.mem_neighborSet, op223_leaf_example, op223_leaf_example,
      SimpleGraph.sup_adj, SimpleGraph.deleteEdges_adj, SimpleGraph.fromEdgeSet_adj,
      SimpleGraph.pathGraph_adj, Set.mem_singleton_iff, Sym2.eq, Finset.mem_coe,
      Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty] <;> decide
  rw [Nat.card_coe_set_eq,h,Set.ncard_coe_finset]
  norm_num [Finset.card_insert_eq_ite, Fin.ext_iff]

lemma op223_leaf_example_degree_1 : Nat.card (op223_leaf_example.neighborSet 1) = 2 := by
  have h : op223_leaf_example.neighborSet 1 = (({0,2} : Finset (Fin 4)) : Set (Fin 4)) := by
    ext x
    fin_cases x <;> simp only [SimpleGraph.mem_neighborSet, op223_leaf_example, op223_leaf_example,
      SimpleGraph.sup_adj, SimpleGraph.deleteEdges_adj, SimpleGraph.fromEdgeSet_adj,
      SimpleGraph.pathGraph_adj, Set.mem_singleton_iff, Sym2.eq, Finset.mem_coe,
      Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty] <;> decide
  rw [Nat.card_coe_set_eq,h,Set.ncard_coe_finset]
  norm_num [Finset.card_insert_eq_ite, Fin.ext_iff]

lemma op223_leaf_example_degree_2 : Nat.card (op223_leaf_example.neighborSet 2) = 2 := by
  have h : op223_leaf_example.neighborSet 2 = (({1,3} : Finset (Fin 4)) : Set (Fin 4)) := by
    ext x
    fin_cases x <;> simp only [SimpleGraph.mem_neighborSet, op223_leaf_example, op223_leaf_example,
      SimpleGraph.sup_adj, SimpleGraph.deleteEdges_adj, SimpleGraph.fromEdgeSet_adj,
      SimpleGraph.pathGraph_adj, Set.mem_singleton_iff, Sym2.eq, Finset.mem_coe,
      Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty] <;> decide
  rw [Nat.card_coe_set_eq,h,Set.ncard_coe_finset]
  norm_num [Finset.card_insert_eq_ite, Fin.ext_iff]

lemma op223_leaf_example_degree_3 : Nat.card (op223_leaf_example.neighborSet 3) = 1 := by
  have h : op223_leaf_example.neighborSet 3 = (({2} : Finset (Fin 4)) : Set (Fin 4)) := by
    ext x
    fin_cases x <;> simp only [SimpleGraph.mem_neighborSet, op223_leaf_example, op223_leaf_example,
      SimpleGraph.sup_adj, SimpleGraph.deleteEdges_adj, SimpleGraph.fromEdgeSet_adj,
      SimpleGraph.pathGraph_adj, Set.mem_singleton_iff, Sym2.eq, Finset.mem_coe,
      Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty] <;> decide
  rw [Nat.card_coe_set_eq,h,Set.ncard_coe_finset]
  norm_num [Finset.card_insert_eq_ite, Fin.ext_iff]

lemma op223_leaf_example_after_degree_0 : Nat.card (op223_leaf_example_after.neighborSet 0) = 0 := by
  have h : op223_leaf_example_after.neighborSet 0 = ((∅ : Finset (Fin 4)) : Set (Fin 4)) := by
    ext x
    fin_cases x <;> simp only [SimpleGraph.mem_neighborSet, op223_leaf_example_after, op223_leaf_example,
      SimpleGraph.sup_adj, SimpleGraph.deleteEdges_adj, SimpleGraph.fromEdgeSet_adj,
      SimpleGraph.pathGraph_adj, Set.mem_singleton_iff, Sym2.eq, Finset.mem_coe,
      Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty] <;> decide
  rw [Nat.card_coe_set_eq,h,Set.ncard_coe_finset]
  norm_num [Finset.card_insert_eq_ite, Fin.ext_iff]

lemma op223_leaf_example_after_degree_1 : Nat.card (op223_leaf_example_after.neighborSet 1) = 2 := by
  have h : op223_leaf_example_after.neighborSet 1 = (({2,3} : Finset (Fin 4)) : Set (Fin 4)) := by
    ext x
    fin_cases x <;> simp only [SimpleGraph.mem_neighborSet, op223_leaf_example_after, op223_leaf_example,
      SimpleGraph.sup_adj, SimpleGraph.deleteEdges_adj, SimpleGraph.fromEdgeSet_adj,
      SimpleGraph.pathGraph_adj, Set.mem_singleton_iff, Sym2.eq, Finset.mem_coe,
      Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty] <;> decide
  rw [Nat.card_coe_set_eq,h,Set.ncard_coe_finset]
  norm_num [Finset.card_insert_eq_ite, Fin.ext_iff]

lemma op223_leaf_example_after_degree_2 : Nat.card (op223_leaf_example_after.neighborSet 2) = 2 := by
  have h : op223_leaf_example_after.neighborSet 2 = (({1,3} : Finset (Fin 4)) : Set (Fin 4)) := by
    ext x
    fin_cases x <;> simp only [SimpleGraph.mem_neighborSet, op223_leaf_example_after, op223_leaf_example,
      SimpleGraph.sup_adj, SimpleGraph.deleteEdges_adj, SimpleGraph.fromEdgeSet_adj,
      SimpleGraph.pathGraph_adj, Set.mem_singleton_iff, Sym2.eq, Finset.mem_coe,
      Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty] <;> decide
  rw [Nat.card_coe_set_eq,h,Set.ncard_coe_finset]
  norm_num [Finset.card_insert_eq_ite, Fin.ext_iff]

lemma op223_leaf_example_after_degree_3 : Nat.card (op223_leaf_example_after.neighborSet 3) = 2 := by
  have h : op223_leaf_example_after.neighborSet 3 = (({1,2} : Finset (Fin 4)) : Set (Fin 4)) := by
    ext x
    fin_cases x <;> simp only [SimpleGraph.mem_neighborSet, op223_leaf_example_after, op223_leaf_example,
      SimpleGraph.sup_adj, SimpleGraph.deleteEdges_adj, SimpleGraph.fromEdgeSet_adj,
      SimpleGraph.pathGraph_adj, Set.mem_singleton_iff, Sym2.eq, Finset.mem_coe,
      Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty] <;> decide
  rw [Nat.card_coe_set_eq,h,Set.ncard_coe_finset]
  norm_num [Finset.card_insert_eq_ite, Fin.ext_iff]

theorem op223_leaf_slide_count_counterexample :
    ∃ (X : SimpleGraph (Fin 4)) (u v b : Fin 4), u ≠ v ∧ b ≠ v ∧ X.Adj u b ∧
      ¬ X.Adj v b ∧ Nat.card (X.neighborSet v) = 1 ∧
      (Finset.univ.filter (fun x : Fin 4 => Nat.card ((X.deleteEdges {s(u,b)} ⊔ SimpleGraph.fromEdgeSet {s(v,b)}).neighborSet x) = 1)).card + 1 <
        (Finset.univ.filter (fun x : Fin 4 => Nat.card (X.neighborSet x) = 1)).card := by
  refine ⟨op223_leaf_example, 0, 3, 1, by decide, by decide, ?_, ?_, op223_leaf_example_degree_3, ?_⟩
  · norm_num [op223_leaf_example, SimpleGraph.pathGraph_adj]
  · norm_num [op223_leaf_example, SimpleGraph.pathGraph_adj]
  · change (Finset.univ.filter (fun x : Fin 4 => Nat.card (op223_leaf_example_after.neighborSet x) = 1)).card + 1 <
      (Finset.univ.filter (fun x : Fin 4 => Nat.card (op223_leaf_example.neighborSet x) = 1)).card
    have ha : Finset.univ.filter (fun x : Fin 4 => Nat.card (op223_leaf_example_after.neighborSet x) = 1) = ∅ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      fin_cases x
      · change ¬ Nat.card (op223_leaf_example_after.neighborSet 0) = 1
        rw [op223_leaf_example_after_degree_0]; decide
      · change ¬ Nat.card (op223_leaf_example_after.neighborSet 1) = 1
        rw [op223_leaf_example_after_degree_1]; decide
      · change ¬ Nat.card (op223_leaf_example_after.neighborSet 2) = 1
        rw [op223_leaf_example_after_degree_2]; decide
      · change ¬ Nat.card (op223_leaf_example_after.neighborSet 3) = 1
        rw [op223_leaf_example_after_degree_3]; decide
    have hb : Finset.univ.filter (fun x : Fin 4 => Nat.card (op223_leaf_example.neighborSet x) = 1) = {0,3} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
      fin_cases x
      · change (Nat.card (op223_leaf_example.neighborSet 0) = 1) ↔ ((0 : Fin 4) = 0 ∨ (0 : Fin 4) = 3)
        rw [op223_leaf_example_degree_0]; decide
      · change (Nat.card (op223_leaf_example.neighborSet 1) = 1) ↔ ((1 : Fin 4) = 0 ∨ (1 : Fin 4) = 3)
        rw [op223_leaf_example_degree_1]; decide
      · change (Nat.card (op223_leaf_example.neighborSet 2) = 1) ↔ ((2 : Fin 4) = 0 ∨ (2 : Fin 4) = 3)
        rw [op223_leaf_example_degree_2]; decide
      · change (Nat.card (op223_leaf_example.neighborSet 3) = 1) ↔ ((3 : Fin 4) = 0 ∨ (3 : Fin 4) = 3)
        rw [op223_leaf_example_degree_3]; decide
    rw [ha,hb]
    norm_num [Finset.card_insert_eq_ite, Fin.ext_iff]
