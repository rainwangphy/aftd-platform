import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TwoAgentDraftWelfare
import AFTD.Kb.GameTheoryEconomics.TwoAgentFirstBestWelfare

/-!
# two_agent_welfare_regret

Topic: fair_division   Node: d4474db51b44

Provenance: formalization of a published result. Source: Kalinowski et al., IJCAI 2013

Given a number of goods m : ℕ, a drafting schedule s : Fin m → Fin 2 of length m, and valuations v : Fin 2 → Fin m → ℝ, the utilitarian welfare regret is the first-best optimal welfare minus the utilitarian welfare of sincere drafting under schedule s.
-/

/-- The utilitarian welfare regret of a two-agent draft schedule s : Fin m → Fin 2 relative to the first-best allocation. -/
noncomputable def two_agent_welfare_regret (m : ℕ) (s : Fin m → Fin 2) (v : Fin 2 → Fin m → ℝ) : ℝ :=
  two_agent_first_best_welfare m v - two_agent_draft_welfare m s v
