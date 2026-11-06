import AFTD.Prelude

/-!
# maxcut_unsafe_pivot_stable_graph

Topic: equilibria   Node: 6de1690c7683

Provenance: helper lemma. Experiments 16728 and 16729.

A six-vertex graph testing whether neutral pivot safety is necessary for a strong extension.
-/

def maxcut_unsafe_pivot_stable_graph : SimpleGraph (Fin 6) := SimpleGraph.fromRel (fun u v : Fin 6 => (u.val, v.val) ∈ [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (1, 5), (2, 3), (2, 5), (4, 5)])
