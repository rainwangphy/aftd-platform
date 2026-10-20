import AFTD.Prelude
import AFTD.Kb.Tcs.CutSeparation
import AFTD.Kb.Tcs.CutCapacity
import AFTD.Kb.Tcs.FlowSupportsRate
import AFTD.Kb.Tcs.FlowCutDivergenceEq
import AFTD.Kb.Tcs.FlowSessionCutDemandEq
import AFTD.Kb.Tcs.CutSeparationEqSum
import AFTD.Kb.Tcs.UnicastSessions
import AFTD.Kb.Tcs.CapacitatedNetwork
import AFTD.Kb.Tcs.IsMulticommodityFlow

/-!
# flow_rate_mul_sep_le_cut_capacity

Topic: information   Node: 23c158bc9573

Provenance: helper lemma. step towards undirected_binary_linear_unicast_advantage

If a fractional multicommodity flow supports the common rate r, then for every vertex set S, r times the number of sessions crossing S is at most the total capacity leaving S.
-/

/-- A flow-supported rate is bounded on every cut by capacity over number of crossing sessions. -/
theorem flow_rate_mul_sep_le_cut_capacity
    {V : Type} [Fintype V] [DecidableEq V] {K : Type} [Fintype K] [DecidableEq K]
    (net : CapacitatedNetwork V) (sess : UnicastSessions V K) {r : ℝ}
    (h : FlowSupportsRate net sess r) (S : Finset V) :
    r * (cutSeparation sess S : ℝ) ≤ cutCapacity net S := by
  obtain ⟨f, hnn, hcap, hdiv⟩ := h
  -- Each session's outflow across the cut, and its inflow across the cut.
  have hout_nn : ∀ k : K, 0 ≤ ∑ v ∈ S, ∑ w, (if w ∈ S then 0 else f k v w) := by
    intro k
    refine Finset.sum_nonneg (fun v _ => ?_)
    refine Finset.sum_nonneg (fun w _ => ?_)
    by_cases hw : w ∈ S
    · simp [hw]
    · simp only [hw, if_false]
      exact hnn k v w
  have hinn_nn : ∀ k : K, 0 ≤ ∑ v ∈ S, ∑ w, (if w ∈ S then 0 else f k w v) := by
    intro k
    refine Finset.sum_nonneg (fun v _ => ?_)
    refine Finset.sum_nonneg (fun w _ => ?_)
    by_cases hw : w ∈ S
    · simp [hw]
    · simp only [hw, if_false]
      exact hnn k w v
  -- Net flow across the cut equals the demand of the session summed over the cut.
  have hdiv_cut : ∀ k : K,
      (∑ v ∈ S, ∑ w, (if w ∈ S then 0 else f k v w)) - (∑ v ∈ S, ∑ w, (if w ∈ S then 0 else f k w v)) =
      (if sess.src k ∈ S ∧ sess.tgt k ∉ S then r else if sess.src k ∉ S ∧ sess.tgt k ∈ S then -r else 0) := by
    intro k
    rw [← flow_cut_divergence_eq (f k) S]
    rw [Finset.sum_congr rfl (fun v _ => hdiv k v)]
    exact flow_session_cut_demand_eq sess r k S
  -- Per session: the total flow across the cut in both directions is at least `r` if the
  -- session crosses the cut, and at least `0` otherwise.
  have hkey : ∀ k : K,
      r * (if sess.src k ∈ S ∧ sess.tgt k ∉ S then (1:ℝ)
        else if sess.src k ∉ S ∧ sess.tgt k ∈ S then 1 else 0) ≤
      (∑ v ∈ S, ∑ w, (if w ∈ S then 0 else f k v w)) + (∑ v ∈ S, ∑ w, (if w ∈ S then 0 else f k w v)) := by
    intro k
    have hD := hdiv_cut k
    have hn1 := hout_nn k
    have hn2 := hinn_nn k
    by_cases hs : sess.src k ∈ S <;> by_cases ht : sess.tgt k ∈ S
    · have hD' : (∑ v ∈ S, ∑ w, (if w ∈ S then 0 else f k v w)) - (∑ v ∈ S, ∑ w, (if w ∈ S then 0 else f k w v)) = 0 := by
        rw [hD]; simp [hs, ht]
      simp [hs, ht]
      linarith
    · have hD' : (∑ v ∈ S, ∑ w, (if w ∈ S then 0 else f k v w)) - (∑ v ∈ S, ∑ w, (if w ∈ S then 0 else f k w v)) = r := by
        rw [hD]; simp [hs, ht]
      simp [hs, ht]
      linarith
    · have hD' : (∑ v ∈ S, ∑ w, (if w ∈ S then 0 else f k v w)) - (∑ v ∈ S, ∑ w, (if w ∈ S then 0 else f k w v)) = -r := by
        rw [hD]; simp [hs, ht]
      simp [hs, ht]
      linarith
    · have hD' : (∑ v ∈ S, ∑ w, (if w ∈ S then 0 else f k v w)) - (∑ v ∈ S, ∑ w, (if w ∈ S then 0 else f k w v)) = 0 := by
        rw [hD]; simp [hs, ht]
      simp [hs, ht]
      linarith
  have hsep_eq : (cutSeparation sess S : ℝ) =
      ∑ k : K, (if sess.src k ∈ S ∧ sess.tgt k ∉ S then (1:ℝ)
        else if sess.src k ∉ S ∧ sess.tgt k ∈ S then 1 else 0) := by
    rw [cutSeparation_eq_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases hs : sess.src k ∈ S <;> by_cases ht : sess.tgt k ∈ S <;> simp [hs, ht]
  -- Lower bound: sum the per-session inequality over all sessions.
  have hsum_lower : r * (cutSeparation sess S : ℝ) ≤
      ∑ k : K, ((∑ v ∈ S, ∑ w, (if w ∈ S then 0 else f k v w)) +
        (∑ v ∈ S, ∑ w, (if w ∈ S then 0 else f k w v))) := by
    rw [hsep_eq, Finset.mul_sum]
    exact Finset.sum_le_sum (fun k _ => hkey k)
  have hmerge : ∀ k : K,
      (∑ v ∈ S, ∑ w, (if w ∈ S then 0 else f k v w)) + (∑ v ∈ S, ∑ w, (if w ∈ S then 0 else f k w v))
      = ∑ v ∈ S, ∑ w, (if w ∈ S then 0 else (f k v w + f k w v)) := by
    intro k
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    by_cases hw : w ∈ S
    · simp [hw]
    · simp only [hw, if_false]
  have hstep : (∑ k : K, ∑ v ∈ S, ∑ w, (if w ∈ S then 0 else (f k v w + f k w v)))
      = ∑ v ∈ S, ∑ w, (if w ∈ S then 0 else ∑ k : K, (f k v w + f k w v)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    by_cases hw : w ∈ S
    · simp [hw]
    · simp only [hw, if_false]
  -- Upper bound: the capacity constraint, summed over the ordered crossing pairs.
  have hbound : (∑ v ∈ S, ∑ w, (if w ∈ S then 0 else ∑ k : K, (f k v w + f k w v)))
      ≤ cutCapacity net S := by
    simp only [cutCapacity]
    refine Finset.sum_le_sum (fun v hv => ?_)
    refine Finset.sum_le_sum (fun w _ => ?_)
    by_cases hw : w ∈ S
    · simp [hw]
    · simp only [hw, if_false]
      exact hcap v w (fun hvw => hw (hvw ▸ hv))
  have hsum_upper : (∑ k : K, ((∑ v ∈ S, ∑ w, (if w ∈ S then 0 else f k v w)) +
        (∑ v ∈ S, ∑ w, (if w ∈ S then 0 else f k w v)))) ≤ cutCapacity net S := by
    have h1 : (∑ k : K, ((∑ v ∈ S, ∑ w, (if w ∈ S then 0 else f k v w)) +
        (∑ v ∈ S, ∑ w, (if w ∈ S then 0 else f k w v))))
        = ∑ k : K, ∑ v ∈ S, ∑ w, (if w ∈ S then 0 else (f k v w + f k w v)) :=
      Finset.sum_congr rfl (fun k _ => hmerge k)
    rw [h1, hstep]
    exact hbound
  exact le_trans hsum_lower hsum_upper
