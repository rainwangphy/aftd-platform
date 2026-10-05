import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Poc8CoverOk

/-!
# poc8_cover_check_4

Topic: fair_division   Node: 12f315a6406d

Kernel check of the cover condition for all terminal tuples with first terminal x = 4.
-/

theorem poc8_cover_check_4 : ∀ y a b c : Fin 8, poc8_cover_ok 4 y a b c = true := by
  decide +kernel
