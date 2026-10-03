import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.WvgWins
import AFTD.Kb.GameTheoryEconomics.Bz3Coal

/-!
# bz3_pattern

Topic: general_equilibrium   Node: 726a6c8e9e04

The winning pattern of the 3-player weighted game (w; 1/2) with strict quota.
-/

/-- The winning pattern of the 3-player game `(w; 1/2)`. -/
noncomputable def bz3_pattern (w : Fin 3 → ℝ) : Fin 8 → Bool :=
  fun k => decide (wvg_wins w (1 / 2) (bz3_coal k))
