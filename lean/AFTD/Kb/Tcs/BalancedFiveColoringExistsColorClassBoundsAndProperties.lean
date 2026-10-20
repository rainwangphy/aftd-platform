import AFTD.Prelude
import AFTD.Kb.Tcs.EdgeColorClassGraph
import AFTD.Kb.Tcs.IsBalancedFiveColoring
import AFTD.Kb.Tcs.GraphHasNoIndepSix
import AFTD.Kb.Tcs.GraphSatisfiesPropertyL
import AFTD.Kb.Tcs.BalancedFiveColoringColorClassPropertyL
import AFTD.Kb.Tcs.BalancedFiveColoringExistsClassCardEdgeFinsetLe65
import AFTD.Kb.Tcs.CardEdgeFinsetGe55OfNoIndepSix

/-!
# balanced_five_coloring_exists_color_class_bounds_and_properties

Topic: combinatorics   Node: f1894c952b09

Provenance: formalization of a published result. Source: scout/2610-24484-erd-h-o-s-gy-arf-as-balanced-five-colorings.md:324

For an arbitrary finite type V with 26 elements, if c : Sym2 V → Fin 5 is a balanced edge coloring, then some color class graph has no independent set of size 6, satisfies property (L), and has between 55 and 65 edges.
-/

/-- Some color class of a balanced 5-coloring of K_26 has alpha <= 5, satisfies property (L), and has between 55 and 65 edges. -/
theorem balanced_five_coloring_exists_color_class_bounds_and_properties
    {V : Type*} [Fintype V] [DecidableEq V]
    (hcard : Fintype.card V = 26) (c : Sym2 V → Fin 5) (hc : is_balanced_five_coloring c) :
    ∃ k : Fin 5,
      graph_has_no_indep_six (edge_color_class_graph c k) ∧
      graph_satisfies_property_l (edge_color_class_graph c k) ∧
      55 ≤ (edge_color_class_graph c k).edgeFinset.card ∧
      (edge_color_class_graph c k).edgeFinset.card ≤ 65 := by
  obtain ⟨k, hk65⟩ := balanced_five_coloring_exists_class_card_edgeFinset_le_65 c hcard
  refine ⟨k, ?_, balanced_five_coloring_color_class_property_l c hc k, ?_, hk65⟩
  · intro S hS
    obtain ⟨v, hv, w, hw, hvw, hc'⟩ := hc S hS k
    exact ⟨v, hv, w, hw, hvw, hc'⟩
  · exact card_edgeFinset_ge_55_of_no_indep_six hcard (edge_color_class_graph c k)
      (fun S hS => by
        obtain ⟨v, hv, w, hw, hvw, hc'⟩ := hc S hS k
        exact ⟨v, hv, w, hw, hvw, hc'⟩)
