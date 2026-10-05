import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AgMP
import AFTD.Kb.GameTheoryEconomics.AgMPv

/-!
# agMP_u_eq

Topic: equilibria   Node: 4c32886ef42a

The rational payoff of matching pennies equals its integer payoff table agMPv.
-/

theorem agMP_u_eq (p i : Fin 2) (y : Fin 2 → ℕ) : agMP.u p i y = (agMPv p i y : ℚ) := by
  simp only [agMP, agMPv]
  split_ifs <;> simp
