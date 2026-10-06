import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongDeviation

/-!
# maxcut_strong_deviation_top_three_constant

Topic: equilibria   Node: 9aafe4590ce8

Provenance: helper lemma. sanity check of is_maxcut_strong_deviation

On the triangle with three colors, from the constant coloring the coalition of two vertices that recolor to the two other colors is a strong deviation.
-/

theorem maxcut_strong_deviation_top_three_constant :
    is_maxcut_strong_deviation (⊤ : SimpleGraph (Fin 3)) (k := 3) ![0, 0, 0] {1, 2} ![0, 1, 2] := by
  unfold is_maxcut_strong_deviation; decide
