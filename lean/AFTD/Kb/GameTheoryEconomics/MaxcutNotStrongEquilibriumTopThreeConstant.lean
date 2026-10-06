import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongEquilibrium
import AFTD.Kb.GameTheoryEconomics.MaxcutStrongDeviationTopThreeConstant

/-!
# maxcut_not_strong_equilibrium_top_three_constant

Topic: equilibria   Node: e62ce995df5d

Provenance: helper lemma. sanity check of is_maxcut_strong_equilibrium

On the triangle with three colors, the constant coloring is not a strong equilibrium.
-/

theorem maxcut_not_strong_equilibrium_top_three_constant :
    ¬ is_maxcut_strong_equilibrium (⊤ : SimpleGraph (Fin 3)) (k := 3) ![0, 0, 0] :=
  fun h => h _ _ maxcut_strong_deviation_top_three_constant
