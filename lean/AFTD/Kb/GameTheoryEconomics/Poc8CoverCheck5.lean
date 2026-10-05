import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Poc8CoverOk

/-!
# poc8_cover_check_5

Topic: fair_division   Node: 5be7834a0c86

Kernel check of the cover condition for all terminal tuples with first terminal x = 5.
-/

theorem poc8_cover_check_5 : ∀ y a b c : Fin 8, poc8_cover_ok 5 y a b c = true := by
  decide +kernel
