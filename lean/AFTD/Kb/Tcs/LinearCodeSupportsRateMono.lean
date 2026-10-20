import AFTD.Prelude
import AFTD.Kb.Tcs.LinearCodeSupportsRate
import AFTD.Kb.Tcs.CausalLinearNetworkCode
import AFTD.Kb.Tcs.UnicastSessions
import AFTD.Kb.Tcs.CapacitatedNetwork

/-!
# linear_code_supports_rate_mono

Topic: information   Node: 07dfbc4056d0

Provenance: helper lemma. folklore

If LinearCodeSupportsRate F net sess r holds on net with sessions sess over field F, then for any r' ≤ r, LinearCodeSupportsRate F net sess r' also holds.
-/

/-- Achievable linear network coding rates are downward-closed. -/
theorem linear_code_supports_rate_mono {V : Type} [Fintype V] [DecidableEq V] {K : Type} [Fintype K] [DecidableEq K]
    (F : Type) [Field F] (net : CapacitatedNetwork V) (sess : UnicastSessions V K) {r r' : ℝ}
    (h_supp : LinearCodeSupportsRate F net sess r) (h_le : r' ≤ r) :
    LinearCodeSupportsRate F net sess r' := by
  obtain ⟨code, hcode⟩ := h_supp
  exact ⟨code, h_le.trans hcode⟩
