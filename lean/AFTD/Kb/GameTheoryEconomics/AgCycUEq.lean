import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AgCyc
import AFTD.Kb.GameTheoryEconomics.AgCycV

/-!
# agCyc_u_eq

Topic: equilibria   Node: 676642c1e046

The payoff of the cyclic anonymous game is the integer table agCycV divided by 4.
-/

theorem agCyc_u_eq {n s : ℕ} [NeZero s] (p : Fin n) (i : Fin s) (y : Fin s → ℕ) :
    (agCyc n s).u p i y = (agCycV i y : ℚ) / 4 := by
  simp [agCyc, agCycV, Nat.cast_min]
