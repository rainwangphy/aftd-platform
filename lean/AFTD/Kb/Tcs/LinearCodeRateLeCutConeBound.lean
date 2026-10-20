import AFTD.Prelude
import AFTD.Kb.Tcs.LinearCodeSupportsRateCutBound
import AFTD.Kb.Tcs.CutSeparation
import AFTD.Kb.Tcs.CutCapacity
import AFTD.Kb.Tcs.UnicastSessions
import AFTD.Kb.Tcs.LinearCodeSupportsRate
import AFTD.Kb.Tcs.CapacitatedNetwork

/-!
# linear_code_rate_le_cut_cone_bound

Topic: information   Node: 0ac7cf97cdc0

Provenance: helper lemma. step towards undirected_binary_linear_unicast_advantage

If a linear network code over a field F supports the common rate r, then for any finite family of vertex sets cuts and any nonnegative weights y on them with positive total weighted separation, r is at most (sum over cuts of y*cutCapacity)/(sum over cuts of y*cutSeparation).
-/

/-- Cut cone bound: a linear code's rate is at most the weighted cut ratio for any nonnegative weighting of cuts. -/
theorem linear_code_rate_le_cut_cone_bound
    {V : Type} [Fintype V] [DecidableEq V] {K : Type} [Fintype K] [DecidableEq K]
    (F : Type) [Field F] (net : CapacitatedNetwork V) (sess : UnicastSessions V K) {r : ℝ}
    (h : LinearCodeSupportsRate F net sess r) (cuts : Finset (Finset V)) (y : Finset V → ℝ)
    (hy : ∀ S ∈ cuts, 0 ≤ y S)
    (hpos : 0 < ∑ S ∈ cuts, y S * (cutSeparation sess S : ℝ)) :
    r ≤ (∑ S ∈ cuts, y S * cutCapacity net S) / (∑ S ∈ cuts, y S * (cutSeparation sess S : ℝ)) := by
  rw [le_div_iff₀ hpos, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro S hS
  have hcut := linear_code_supports_rate_cut_bound F net sess h S
  have hyS := hy S hS
  nlinarith
