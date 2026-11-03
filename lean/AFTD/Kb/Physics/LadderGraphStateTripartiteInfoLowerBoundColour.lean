import AFTD.Prelude
import AFTD.Kb.Physics.LadderGraphStateTripartiteInfoLowerBoundPairCode

/-!
# ladder_graph_state_tripartite_info_lower_bound_colour

Topic: quantum_mechanics   Node: 83d641361537

Provenance: helper lemma. step towards ladder_graph_state_tripartite_info_lower_bound

The four-colouring of the ladder's vertices: vertex (i,0) gets the high nibble of rung code i (i.e. pair_code i / 4), vertex (i,1) the low nibble (pair_code i mod 4), reduced mod 4 into Fin 4.
-/

/-- Vertex colour of the ladder witness: channel `a` of rung `i` gets a nibble of the rung code. -/
def ladder_graph_state_tripartite_info_lower_bound_colour (n : ℕ) (v : Fin n × Fin 2) : Fin 4 := ⟨(if v.2 = (0 : Fin 2) then
        ladder_graph_state_tripartite_info_lower_bound_pair_code v.1 / 4
      else ladder_graph_state_tripartite_info_lower_bound_pair_code v.1) % 4,
    Nat.mod_lt _ (by norm_num)⟩
