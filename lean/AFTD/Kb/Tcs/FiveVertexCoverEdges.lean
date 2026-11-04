import AFTD.Prelude

/-!
# five_vertex_cover_edges

Topic: combinatorics   Node: 8fc336e656db

Provenance: helper lemma. step towards simple_graph_five_noncycle_independent_cover_witness

The six representative edge sets on vertex set Fin 5, one per isomorphism type of triangle-free five-vertex graph with no isolated vertex that is not 2-regular: 0 = P3 plus a disjoint edge {01,02,34}; 1 = the 4-star K_{1,4} {01,02,03,04}; 2 = the 3-star with a pendant on one leaf {01,02,03,14}; 3 = the 5-path P5 {01,02,13,24}; 4 = the 5-edge type {01,02,03,14,24}; 5 = K_{2,3} {01,02,03,14,24,34}.
-/

/-- The six representative edge sets, indexed 0..5, one per isomorphism type in the target class. -/
def five_vertex_cover_edges : Fin 6 → Finset (Sym2 (Fin 5)) := fun i => match i with
  | 0 => {s(0,1), s(0,2), s(3,4)}
  | 1 => {s(0,1), s(0,2), s(0,3), s(0,4)}
  | 2 => {s(0,1), s(0,2), s(0,3), s(1,4)}
  | 3 => {s(0,1), s(0,2), s(1,3), s(2,4)}
  | 4 => {s(0,1), s(0,2), s(0,3), s(1,4), s(2,4)}
  | 5 => {s(0,1), s(0,2), s(0,3), s(1,4), s(2,4), s(3,4)}
