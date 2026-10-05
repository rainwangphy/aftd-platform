import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Poc8CoverOk

/-!
# poc8_cover_check_0

Topic: fair_division   Node: 786f0d892512

Kernel check of the cover condition for all terminal tuples with first terminal x = 0.
-/

theorem poc8_cover_check_0 : ∀ y a b c : Fin 8, poc8_cover_ok 0 y a b c = true := by
  decide +kernel
