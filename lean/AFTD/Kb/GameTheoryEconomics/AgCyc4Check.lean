import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AgCycV
import AFTD.Kb.GameTheoryEconomics.AgSub

/-!
# agCyc4_check

Topic: equilibria   Node: 8486863d1bf7

Finite check for four strategies and five players.
-/

/-- Finite check for four strategies and five players. -/
theorem agCyc4_check : ∀ a b d e : Fin 6, a.val + b.val + d.val + e.val = 5 → ∃ i j : Fin 4,
    0 < (![a.val, b.val, d.val, e.val] i) ∧
    agCycV i (agSub ![a.val, b.val, d.val, e.val] i) + 2 ≤
      agCycV j (agSub ![a.val, b.val, d.val, e.val] i) := by
  decide
