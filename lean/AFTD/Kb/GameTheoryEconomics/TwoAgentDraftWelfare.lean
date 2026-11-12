import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BalancedDraftValueOrder
import AFTD.Kb.GameTheoryEconomics.DraftRule

/-!
# two_agent_draft_welfare

Topic: fair_division   Node: 5195765dc55a

Provenance: formalization of a published result. Source: Kalinowski et al., IJCAI 2013

Given a number of goods m : ℕ, a drafting schedule s : Fin m → Fin 2 of length m, and a valuation profile v : Fin 2 → Fin m → ℝ, the utilitarian social welfare of the two-agent allocation produced by sincere drafting is the sum over both agents i : Fin 2 of their bundle values under draft_rule s.
-/

/-- The utilitarian welfare of a two-agent draft allocation of m goods under schedule s : Fin m → Fin 2 and valuations v. -/
noncomputable def two_agent_draft_welfare (m : ℕ) (s : Fin m → Fin 2) (v : Fin 2 → Fin m → ℝ) : ℝ :=
  ∑ i : Fin 2, ∑ g ∈ draft_rule s (fun j => balanced_draft_value_order (v j)) i, v i g
