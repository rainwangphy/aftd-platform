import AFTD.Prelude

/-!
# net_graph

Topic: graphs   Node: 322da760783c

Provenance: helper lemma. step towards p7_claw_free_dominating_pair_of_no_hole

The net graph on 6 vertices: the triangle {0,4,5} with a pendant leaf (3, 1, 2 respectively) attached to each triangle vertex; edges 03, 04, 05, 14, 25, 45. Lifted to `ULift (Fin 6)` so it inhabits an arbitrary universe `Type u`, which is required to refute a statement universally quantified over `V : Type*`.
-/

/-- The net graph (triangle with one pendant vertex on each triangle vertex), universe-lifted to `ULift (Fin 6)`. -/
def net_graph : SimpleGraph (ULift (Fin 6)) := SimpleGraph.fromRel (fun a b : ULift (Fin 6) =>
    (a.down = 0 ∧ (b.down = 3 ∨ b.down = 4 ∨ b.down = 5)) ∨
    (a.down = 1 ∧ b.down = 4) ∨ (a.down = 2 ∧ b.down = 5) ∨ (a.down = 4 ∧ b.down = 5))
