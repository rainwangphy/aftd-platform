import AFTD.Prelude

/-!
# maxcut_three_leaf_star_graph

Topic: equilibria   Node: 5ad7d414ecd8

Provenance: helper lemma. A four-vertex obstruction to a stronger fixed-profile vertex extension, experiment 16369.

The three-leaf star, with vertex zero at the center.
-/

def maxcut_three_leaf_star_graph : SimpleGraph (Fin 4) := SimpleGraph.fromRel (fun u v : Fin 4 => u.val = 0 ∨ v.val = 0)
