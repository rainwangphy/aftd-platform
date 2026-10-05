import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Poc8CoverOk

/-!
# poc8_cover_check_7

Topic: fair_division   Node: 699cc3bb730b

Kernel check of the cover condition for all terminal tuples with first terminal x = 7.
-/

theorem poc8_cover_check_7 : ∀ y a b c : Fin 8, poc8_cover_ok 7 y a b c = true := by
  decide +kernel
