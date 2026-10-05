import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Poc8CoverCheck0
import AFTD.Kb.GameTheoryEconomics.Poc8CoverCheck1
import AFTD.Kb.GameTheoryEconomics.Poc8CoverCheck2
import AFTD.Kb.GameTheoryEconomics.Poc8CoverCheck3
import AFTD.Kb.GameTheoryEconomics.Poc8CoverCheck4
import AFTD.Kb.GameTheoryEconomics.Poc8CoverCheck5
import AFTD.Kb.GameTheoryEconomics.Poc8CoverCheck6
import AFTD.Kb.GameTheoryEconomics.Poc8CoverCheck7
import AFTD.Kb.GameTheoryEconomics.Poc8CoverOk

/-!
# poc8_cover_check

Topic: fair_division   Node: 0f390098697a

The cover condition holds for all terminal tuples (x, y, a, b, c).
-/

theorem poc8_cover_check (x y a b c : Fin 8) : poc8_cover_ok x y a b c = true := by
  fin_cases x
  exacts [poc8_cover_check_0 y a b c, poc8_cover_check_1 y a b c, poc8_cover_check_2 y a b c,
    poc8_cover_check_3 y a b c, poc8_cover_check_4 y a b c, poc8_cover_check_5 y a b c,
    poc8_cover_check_6 y a b c, poc8_cover_check_7 y a b c]
