import AFTD.Prelude

/-!
# two_agent_first_best_welfare

Topic: fair_division   Node: dc4e1bae698b

Provenance: formalization of a published result. Source: Kalinowski et al., IJCAI 2013

The first-best utilitarian welfare for two agents over m goods, defined as the sum over all goods of the maximum value assigned by either agent.
-/

/-- The first-best optimal utilitarian welfare allocating each good to the agent who values it most. -/
noncomputable def two_agent_first_best_welfare (m : ℕ) (v : Fin 2 → Fin m → ℝ) : ℝ :=
  ∑ g : Fin m, max (v 0 g) (v 1 g)
