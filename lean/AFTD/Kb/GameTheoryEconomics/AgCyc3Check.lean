import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AgCycV
import AFTD.Kb.GameTheoryEconomics.AgSub

/-!
# agCyc3_check

Topic: equilibria   Node: dcfe98d4bc08

Finite check for three strategies and five players (totals a + b + d = 5).
-/

/-- Finite check for three strategies and five players (totals `a + b + d = 5`). -/
theorem agCyc3_check : ∀ a b d : Fin 6, a.val + b.val + d.val = 5 → ∃ i j : Fin 3,
    0 < (![a.val, b.val, d.val] i) ∧
    agCycV i (agSub ![a.val, b.val, d.val] i) + 2 ≤ agCycV j (agSub ![a.val, b.val, d.val] i) := by
  decide
