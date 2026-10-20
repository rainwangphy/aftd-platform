import AFTD.Prelude
import AFTD.Kb.Tcs.EdgeColorClassGraph

/-!
# balanced_five_coloring_exists_class_card_edgeFinset_le_65

Topic: combinatorics   Node: 445c0a3abd72

Provenance: formalization of a published result. Source: scout/2610-24484-erd-h-o-s-gy-arf-as-balanced-five-colorings.md:1287

For an arbitrary finite type V with 26 elements, in any edge coloring c : Sym2 V → Fin 5, some color class graph has at most 65 edges.
-/

lemma balanced_five_coloring_exists_class_card_edgeFinset_le_65_key_edge
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : Sym2 V → Fin 5) (k : Fin 5) :
    (edge_color_class_graph c k).edgeFinset = (⊤ : SimpleGraph V).edgeFinset.filter (fun e => c e = k) := by
  ext e
  rw [SimpleGraph.mem_edgeFinset, Finset.mem_filter, SimpleGraph.mem_edgeFinset]
  induction e using Sym2.ind with
  | _ a b =>
    simp only [SimpleGraph.mem_edgeSet, edge_color_class_graph, SimpleGraph.top_adj]

lemma balanced_five_coloring_exists_class_card_edgeFinset_le_65_sum_class_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : Sym2 V → Fin 5) :
    ∑ k : Fin 5, (edge_color_class_graph c k).edgeFinset.card = (⊤ : SimpleGraph V).edgeFinset.card := by
  simp only [balanced_five_coloring_exists_class_card_edgeFinset_le_65_key_edge]
  rw [Finset.card_eq_sum_card_fiberwise (s := (⊤ : SimpleGraph V).edgeFinset) (f := c) (t := Finset.univ)]
  simp

/-- In any 5-coloring of K_26, some color class has at most 65 edges. -/
theorem balanced_five_coloring_exists_class_card_edgeFinset_le_65
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : Sym2 V → Fin 5) (hcard : Fintype.card V = 26) :
    ∃ k : Fin 5, (edge_color_class_graph c k).edgeFinset.card ≤ 65 := by
  by_contra h
  push Not at h
  have hsum := balanced_five_coloring_exists_class_card_edgeFinset_le_65_sum_class_card c
  rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two, hcard] at hsum
  have hch : Nat.choose 26 2 = 325 := by decide
  rw [hch] at hsum
  have hlower : (∑ k : Fin 5, (edge_color_class_graph c k).edgeFinset.card) ≥ 5 * 66 := by
    calc ∑ k : Fin 5, (edge_color_class_graph c k).edgeFinset.card
        ≥ ∑ _k : Fin 5, 66 := by
          apply Finset.sum_le_sum
          intro k _
          have := h k
          omega
      _ = 5 * 66 := by simp
  omega
