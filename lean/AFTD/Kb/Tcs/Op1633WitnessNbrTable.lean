import AFTD.Prelude

/-!
# op1633_witness_nbr_table

Topic: graphs   Node: f0b9ffabb9d7

Provenance: helper lemma. step towards op_1633_exists_cubic_bipartite_connectivity_two_not_fall_three

The neighbour table of the order-12 witness graph G*: entry u lists the three neighbours of vertex u (the two copies are {0,1,2}/{6,7,8} and {3,4,5}/{9,10,11} of K3,3 minus an edge, joined by 0--9 and 3--6).
-/

/-- Neighbour table (as explicit Nat lists) of the 12-vertex cubic bipartite witness graph. -/
def op1633_witness_nbr_table : List (List Nat) := [[7, 8, 9], [6, 7, 8], [6, 7, 8], [10, 11, 6], [9, 10, 11], [9, 10, 11],
    [1, 2, 3], [0, 1, 2], [0, 1, 2], [0, 4, 5], [3, 4, 5], [3, 4, 5]]
