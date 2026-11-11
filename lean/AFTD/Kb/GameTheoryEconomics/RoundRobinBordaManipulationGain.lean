import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RoundRobinUBest
import AFTD.Kb.GameTheoryEconomics.RoundRobinUTruth

/-!
# round_robin_borda_manipulation_gain

Topic: fair_division   Node: 1ab4bc5edd9d

Provenance: formalization of a published result. Source: Algorithms for Manipulating Sequential Allocation (AAAI 2020)

The real-valued normalized strategic manipulation gain ((round_robin_u_best m rA rB : ℝ) - (round_robin_u_truth m rA rB : ℝ)) / (m : ℝ)^2 for agent A in the two-agent alternating Round-Robin draft of m goods, returning a real number.
-/

/-- Normalized Borda strategic manipulation gain (U_best - U_truth) / m^2 in ℝ for agent A in alternating draft. -/
noncomputable def round_robin_borda_manipulation_gain (m : ℕ) (rA rB : Fin m ≃ Fin m) : ℝ :=
  ((round_robin_u_best m rA rB : ℝ) - (round_robin_u_truth m rA rB : ℝ)) / (m : ℝ)^2
