import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutWelfare

/-!
# maxcut_welfare_top_three_rainbow

Topic: equilibria   Node: fadfbcd25ba4

Provenance: helper lemma. sanity check of maxcut_welfare

On the triangle, the coloring with three distinct colors has social welfare 6 (all three edges cut, each counted twice).
-/

theorem maxcut_welfare_top_three_rainbow :
    maxcut_welfare (⊤ : SimpleGraph (Fin 3)) (k := 3) ![0, 1, 2] = 6 := by decide
