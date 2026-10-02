import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExchangeEconomy
import AFTD.Kb.GameTheoryEconomics.IsFeasibleAllocation

/-!
# endowment_is_feasible

Topic: general_equilibrium   Node: 59433021866c

In any pure exchange economy with finite agents, the initial endowment allocation is feasible.
-/

/-- The initial endowment allocation is always feasible in a pure exchange economy. -/
theorem endowment_is_feasible {Agent Good : Type*} [Fintype Agent] (E : ExchangeEconomy Agent Good) : is_feasible_allocation E E.endowment := ⟨E.endowment_nonneg, fun _ => le_rfl⟩
