import AFTD.Prelude

/-!
# maxcut_defect_one_dense_core_coloring

Topic: equilibria   Node: 4a05540567d2

Provenance: helper lemma. Explicit dense-core example investigated in experiment 16301.

The three part colors of the dense-core witness.
-/

def maxcut_defect_one_dense_core_coloring (v : Fin 12) : Fin 3 := ⟨v.val / 4, by omega⟩
