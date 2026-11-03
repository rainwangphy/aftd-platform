import AFTD.Prelude
import AFTD.Kb.Tcs.TriangleHypergraphObstruction11

/-!
# triangle_hypergraph_obstruction11_properties

Topic: graphs   Node: 211dc986cfe3

Provenance: helper lemma. Finite obstruction to the linear degree-three hypergraph route for the triangle packing-cover problem; experiments 13111, 13112, 13120. No novelty is claimed for the isolated example.

The explicit list has eleven 3-element triples, any two distinct triples meet in at most one point, and every point belongs to exactly three triples. Every selection of three triples contains an intersecting pair, while two displayed triples are disjoint; every selection of five contains a disjoint pair. Every set of at most four points misses some triple, whereas the displayed five-point set meets them all. Hence the packing number is two and the cover number is five, even though no five triples pairwise intersect.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem triangle_hypergraph_obstruction11_properties :
    triangle_hypergraph_obstruction11.length = 11 ∧
    triangle_hypergraph_obstruction11.all (fun e => decide (e.card = 3)) = true ∧
    triangle_hypergraph_obstruction11.all (fun e =>
      triangle_hypergraph_obstruction11.all (fun f =>
        decide (e = f ∨ (e ∩ f).card ≤ 1))) = true ∧
    (∀ v : Fin 11, (triangle_hypergraph_obstruction11.filter fun e => v ∈ e).length = 3) ∧
    ((List.sublistsLen 3 triangle_hypergraph_obstruction11).all fun P =>
      P.any fun e => P.any fun f => decide (e ≠ f ∧ ¬ Disjoint e f)) = true ∧
    ((List.sublistsLen 5 triangle_hypergraph_obstruction11).all fun P =>
      P.any fun e => P.any fun f => decide (Disjoint e f)) = true ∧
    (∀ F : Finset (Fin 11), F.card ≤ 4 →
      (triangle_hypergraph_obstruction11.any fun e => decide (Disjoint F e)) = true) ∧
    (let F : Finset (Fin 11) := {0,1,2,3,5}
     F.card = 5 ∧ triangle_hypergraph_obstruction11.all
       (fun e => decide (¬ Disjoint F e)) = true) ∧
    ({0,1,2} : Finset (Fin 11)) ∈ triangle_hypergraph_obstruction11 ∧
    ({3,4,5} : Finset (Fin 11)) ∈ triangle_hypergraph_obstruction11 ∧
    Disjoint ({0,1,2} : Finset (Fin 11)) {3,4,5} := by
  decide
