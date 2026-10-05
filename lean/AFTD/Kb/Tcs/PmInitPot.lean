import AFTD.Prelude
import AFTD.Kb.Tcs.PMState
import AFTD.Kb.Tcs.PMStatePot
import AFTD.Kb.Tcs.PmInit

/-!
# pm_init_pot

Topic: algorithms   Node: 20da9c518d89

The potential of the initial adversary state is 2n - 3.
-/

open Finset in
theorem pm_init_pot (n : ℕ) : (pmInit n).pot = 2 * (n : ℤ) - 3 := by
  simp only [PMState.pot, pmInit, Finset.image_id, Finset.card_univ, Fintype.card_fin]
  ring
