import AFTD.Prelude
import AFTD.Kb.Tcs.TriangleHypergraphObstruction
import AFTD.Kb.Tcs.TriangleHypergraphObstructionProperties

/-!
# triangle_hypergraph_stable_minimum_cover_incompatible_pair

Topic: graphs   Node: 90eafaa7cd29

Provenance: helper lemma. Experiment 16046 and the existing certified six-triple obstruction.

In the existing six-triple linear obstruction, every point is active and can be omitted by a maximum one-triple packing; the triple {0,1,6} is a maximum packing, {1,2,4} is a minimum cover, and its two points 2 and 4 outside the packing do not occur together in any maximum packing.
-/

theorem triangle_hypergraph_stable_minimum_cover_incompatible_pair :
    ({0,1,6} : Finset (Fin 7)) ∈ triangle_hypergraph_obstruction ∧
    (∀ x : Fin 7, ∃ t ∈ triangle_hypergraph_obstruction, x ∈ t) ∧
    (∀ x : Fin 7, ∃ t ∈ triangle_hypergraph_obstruction, x ∉ t) ∧
    (∀ t ∈ triangle_hypergraph_obstruction,
      ¬ Disjoint ({1,2,4} : Finset (Fin 7)) t) ∧
    (2 : Fin 7) ∉ ({0,1,6} : Finset (Fin 7)) ∧
    (4 : Fin 7) ∉ ({0,1,6} : Finset (Fin 7)) ∧
    (∀ t ∈ triangle_hypergraph_obstruction, ¬ ((2 : Fin 7) ∈ t ∧ (4 : Fin 7) ∈ t)) := by
  decide
