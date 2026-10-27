import AFTD.Prelude
import AFTD.Kb.Tcs.AdmitsSharpCyclicLabeling
import AFTD.Kb.Tcs.IsCirculantGraph
import AFTD.Kb.Tcs.OrderEightHankelAdmitsSharpCyclicLabeling
import AFTD.Kb.Tcs.OrderEightHankelNotCirculant

/-!
# exists_non_circulant_sharp_cyclic_graph_order_eight

Topic: combinatorics   Node: 6686a42efcf5

Provenance: original. Related work: arXiv:2610.31807 Question 12.1

There exists a simple graph G on ZMod 8 with at least one edge that admits a sharp cyclic labeling and is not a circulant graph on ZMod 8.
-/

/-- The Hankel-type adjacency relation on `ZMod 8`: `x ~ y` iff `(x + y).val ∈ {1, 3, 5}`. -/
private abbrev exists_non_circulant_sharp_cyclic_graph_order_eight_hankelRel
    (x y : ZMod 8) : Prop :=
  (x + y).val = 1 ∨ (x + y).val = 3 ∨ (x + y).val = 5

/-- The Hankel-type non-circulant graph on `ZMod 8` witnessing the statement. -/
private abbrev exists_non_circulant_sharp_cyclic_graph_order_eight_hankelGraph :
    SimpleGraph (ZMod 8) :=
  SimpleGraph.mk exists_non_circulant_sharp_cyclic_graph_order_eight_hankelRel
    ⟨fun x y h => by
      simpa only [exists_non_circulant_sharp_cyclic_graph_order_eight_hankelRel, add_comm]
        using h⟩
    ⟨fun x h =>
      (by decide : ∀ x : ZMod 8,
        ¬ exists_non_circulant_sharp_cyclic_graph_order_eight_hankelRel x x) x h⟩

/-- The Hankel-type graph has decidable adjacency. -/
private instance exists_non_circulant_sharp_cyclic_graph_order_eight_hankelGraph_inst :
    DecidableRel exists_non_circulant_sharp_cyclic_graph_order_eight_hankelGraph.Adj :=
  fun x y =>
    (by unfold exists_non_circulant_sharp_cyclic_graph_order_eight_hankelRel; infer_instance :
      Decidable (exists_non_circulant_sharp_cyclic_graph_order_eight_hankelRel x y))

/-- There exists a simple graph on 8 vertices with at least one edge that admits a sharp cyclic labeling and is not circulant. -/
theorem exists_non_circulant_sharp_cyclic_graph_order_eight :
    ∃ (G : SimpleGraph (ZMod 8)) (_ : DecidableRel G.Adj),
      (∃ u v, G.Adj u v) ∧ admits_sharp_cyclic_labeling 8 G ∧ ¬ is_circulant_graph 8 G := ⟨exists_non_circulant_sharp_cyclic_graph_order_eight_hankelGraph,
  exists_non_circulant_sharp_cyclic_graph_order_eight_hankelGraph_inst,
  ⟨0, 1, by decide⟩,
  order_eight_hankel_admits_sharp_cyclic_labeling
    exists_non_circulant_sharp_cyclic_graph_order_eight_hankelGraph (fun _ _ => Iff.rfl),
  order_eight_hankel_not_circulant
    exists_non_circulant_sharp_cyclic_graph_order_eight_hankelGraph (fun _ _ => Iff.rfl)⟩
