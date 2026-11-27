import AFTD.Prelude

/-!
# op309_g6_selected_list

Topic: graphs   Node: 3d8d076345da

Provenance: helper lemma. step towards op309_girth6_source_forest_clique5_nonfive_example

The 24 selected edges: the twelve two-edge paths with centres 0,3,6,...,33 and leaves 3k+1, 3k+2.
-/

/-- The 24 selected edges forming twelve disjoint two-edge paths. -/
def op309_g6_selected_list : List (ℕ × ℕ) := [(0,1), (0,2), (3,4), (3,5), (6,7), (6,8), (9,10), (9,11), (12,13), (12,14), (15,16), (15,17), (18,19), (18,20), (21,22), (21,23), (24,25), (24,26), (27,28), (27,29), (30,31), (30,32), (33,34), (33,35)]
