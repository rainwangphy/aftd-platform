import AFTD.Prelude
import AFTD.Kb.Tcs.LinearCodeSupportsRateCutBound
import AFTD.Kb.Tcs.LinearCodeSupportsRate
import AFTD.Kb.Tcs.CausalLinearNetworkCode
import AFTD.Kb.Tcs.UnicastSessions
import AFTD.Kb.Tcs.CapacitatedNetwork
import AFTD.Kb.Tcs.CutCapacity
import AFTD.Kb.Tcs.CutSeparation

/-!
# one_slot_code_rate_le_cut_ratio

Topic: information   Node: 926820ec053c

Provenance: helper lemma. step towards single_slot_binary_linear_coding_advantage

A one-slot (T = 1) causal linear code over any field satisfies L * (number of sessions separated by S) ≤ (capacity leaving S) for every vertex set S: with one transmission slot the common rate of the code is exactly its message dimension L, so the general cut bound applies with r = L.
-/

/-- A one-slot code's message dimension is bounded by every cut ratio cap(δS)/sep(S). -/
theorem one_slot_code_rate_le_cut_ratio
    {V : Type} [Fintype V] [DecidableEq V] {K : Type} [Fintype K] [DecidableEq K]
    (F : Type) [Field F] (net : CapacitatedNetwork V) (sess : UnicastSessions V K)
    (code : CausalLinearNetworkCode V K F net sess) (hT : code.T = 1) (S : Finset V) :
    (code.L : ℝ) * (cutSeparation sess S : ℝ) ≤ cutCapacity net S := by
  apply linear_code_supports_rate_cut_bound F net sess (r := (code.L : ℝ)) (S := S)
  unfold LinearCodeSupportsRate
  exact ⟨code, by rw [hT]; simp⟩
