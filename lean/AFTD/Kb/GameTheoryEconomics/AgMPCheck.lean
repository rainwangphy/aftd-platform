import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AgCnt
import AFTD.Kb.GameTheoryEconomics.AgMPv

/-!
# agMP_check

Topic: equilibria   Node: 65f8238a541e

Finite check: in matching pennies, every pure profile ![a, b] leaves some player with regret at least 1.
-/

/-- Finite check: in matching pennies, every pure profile `![a, b]` leaves some player with regret at least `1`. -/
theorem agMP_check : ∀ a b : Fin 2, ∃ p j : Fin 2,
    agMPv p (![a, b] p) (agCnt ![a, b] p) + 1 ≤ agMPv p j (agCnt ![a, b] p) := by
  decide
