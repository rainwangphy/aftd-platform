import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExchangeEconomy
import AFTD.Kb.GameTheoryEconomics.IsFeasibleAllocation

/-!
# endowment_is_feasible

Topic: general_equilibrium   Node: 59433021866c

Provenance: original. Related work: machine-posed degenerate case of feasibility in a pure exchange economy (the endowment itself); trivial, no novelty claimed

In any pure exchange economy with finite agents, the initial endowment allocation is feasible.
-/

/-- The initial endowment allocation is always feasible in a pure exchange economy. -/
theorem endowment_is_feasible {Agent Good : Type*} [Fintype Agent] (E : ExchangeEconomy Agent Good) : is_feasible_allocation E E.endowment := ⟨E.endowment_nonneg, fun _ => le_rfl⟩
