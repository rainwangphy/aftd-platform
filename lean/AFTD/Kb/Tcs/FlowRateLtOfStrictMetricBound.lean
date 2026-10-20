import AFTD.Prelude
import AFTD.Kb.Tcs.FlowRateMulTwoLeSumCapMulDist
import AFTD.Kb.Tcs.FlowSupportsRate
import AFTD.Kb.Tcs.CapacitatedNetwork
import AFTD.Kb.Tcs.UnicastSessions

/-!
# flow_rate_lt_of_strict_metric_bound

Topic: information   Node: 68fafd6527c3

Provenance: helper lemma. step towards undirected_binary_linear_unicast_advantage

If a fractional multicommodity flow supports common rate r on net with sessions sess, and d is a nonnegative, symmetric, triangle-satisfying function on V with d(u,u) = 0 and positive total session length sum_k d(src k, tgt k), and the capacity-weighted total length is strictly less than 2*c times the total session length, then r < c.
-/

/-- A strict pseudometric certificate caps every fractional flow rate strictly below c. -/
theorem flow_rate_lt_of_strict_metric_bound
    {V : Type} [Fintype V] [DecidableEq V] {K : Type} [Fintype K] [DecidableEq K]
    (net : CapacitatedNetwork V) (sess : UnicastSessions V K) {r c : ℝ}
    (h : FlowSupportsRate net sess r) (d : V → V → ℝ)
    (h_nonneg : ∀ u v, 0 ≤ d u v) (h_symm : ∀ u v, d u v = d v u)
    (h_diag : ∀ u, d u u = 0) (h_tri : ∀ u v w, d u v ≤ d u w + d w v)
    (hpos : 0 < ∑ k, d (sess.src k) (sess.tgt k))
    (hlt : ∑ u, ∑ v, net.cap s(u, v) * d u v < 2 * c * (∑ k, d (sess.src k) (sess.tgt k))) :
    r < c := by
  have hmain := flow_rate_mul_two_le_sum_cap_mul_dist net sess h d h_nonneg h_symm h_diag h_tri
  nlinarith
