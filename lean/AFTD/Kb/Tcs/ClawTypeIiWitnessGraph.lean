import AFTD.Prelude

/-!
# claw_type_ii_witness_graph

Topic: graphs   Node: 4759dcd3d674

Provenance: helper lemma. step towards exists_claw_free_minimal_3_factor_critical_type_ii_edge

The 15-edge graph on 7 vertices that is the complement of {01, 03, 12, 23, 45, 56}, lifted to universe u, defined by an explicit decidable edge predicate.
-/

/-- The 7-vertex witness graph (lifted to universe `u`): the complement of the 6-edge graph {01,03,12,23,45,56}. -/
def claw_type_ii_witness_graph.{u} : SimpleGraph (ULift.{u, 0} (Fin 7)) := SimpleGraph.fromRel fun a b : ULift.{u, 0} (Fin 7) =>
  s(a.down, b.down) ∉ ({s(0, 1), s(0, 3), s(1, 2), s(2, 3), s(4, 5), s(5, 6)} : Finset (Sym2 (Fin 7)))
