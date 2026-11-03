import AFTD.Prelude
import AFTD.Kb.Physics.LadderGraphStateTripartiteInfoLowerBoundColour

/-!
# ladder_graph_state_tripartite_info_lower_bound_part

Topic: quantum_mechanics   Node: d0f84c6244c6

Provenance: helper lemma. step towards ladder_graph_state_tripartite_info_lower_bound

The part of colour c: the finset of all ladder vertices whose colour is c.
-/

/-- The part of colour `c`: the fibre of the vertex colouring. -/
noncomputable def ladder_graph_state_tripartite_info_lower_bound_part (n : ℕ) (c : Fin 4) : Finset (Fin n × Fin 2) := Finset.univ.filter (fun v => ladder_graph_state_tripartite_info_lower_bound_colour n v = c)
