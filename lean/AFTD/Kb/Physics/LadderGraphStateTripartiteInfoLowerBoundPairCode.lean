import AFTD.Prelude

/-!
# ladder_graph_state_tripartite_info_lower_bound_pair_code

Topic: quantum_mechanics   Node: 6eb998b87412

Provenance: helper lemma. step towards ladder_graph_state_tripartite_info_lower_bound

The rung code of rung i of the 2-by-n ladder: 1 for rung 0, then the period-9 word 6,14,2,8,12,4,1,13,9 (each code is a hex pair: code/4 = colour of the top vertex, code%4 = colour of the bottom vertex).
-/

/-- Rung code: 1 for rung 0, else the length-9 motif 6,14,2,8,12,4,1,13,9. -/
def ladder_graph_state_tripartite_info_lower_bound_pair_code (i : ℕ) : ℕ := if i = 0 then 1 else [6, 14, 2, 8, 12, 4, 1, 13, 9].getD ((i - 1) % 9) 0
