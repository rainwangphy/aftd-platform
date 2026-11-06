import AFTD.Prelude

/-!
# maxcut_defect_one_dense_core_graph

Topic: equilibria   Node: 6e03205ca151

Provenance: helper lemma. Explicit dense-core example investigated in experiment 16301.

The join of three disjoint four-vertex matchings.
-/

def maxcut_defect_one_dense_core_graph : SimpleGraph (Fin 12) := SimpleGraph.fromRel (fun u v : Fin 12 => u.val / 4 ≠ v.val / 4 ∨ u.val / 2 = v.val / 2)
