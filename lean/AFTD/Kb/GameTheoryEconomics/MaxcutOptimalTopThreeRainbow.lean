import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsMaxcutOptimal

/-!
# maxcut_optimal_top_three_rainbow

Topic: equilibria   Node: 76e52cfe8628

Provenance: helper lemma. sanity check of is_maxcut_optimal

On the triangle with three colors, the rainbow coloring is optimal.
-/

theorem maxcut_optimal_top_three_rainbow :
    is_maxcut_optimal (⊤ : SimpleGraph (Fin 3)) (k := 3) ![0, 1, 2] := by
  unfold is_maxcut_optimal; decide
