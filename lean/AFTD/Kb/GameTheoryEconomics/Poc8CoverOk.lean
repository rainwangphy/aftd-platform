import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Poc8Cands

/-!
# poc8_cover_ok

Topic: fair_division   Node: f39f6baa0ce9

Check for terminals x, y, a, b, c: either they are not distinct, or some stored mask contains x and y and avoids a, b, c.
-/

/-- Terminals are not distinct, or some stored mask contains `x, y` and avoids `a, b, c`. -/
def poc8_cover_ok (x y a b c : Fin 8) : Bool :=
  x == y || a == b || a == c || b == c || x == a || x == b || x == c || y == a || y == b ||
    y == c || poc8_cands.any fun m =>
      m.testBit x && m.testBit y && !m.testBit a && !m.testBit b && !m.testBit c
