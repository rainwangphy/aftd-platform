import AFTD.Prelude
import AFTD.Kb.Tcs.CapacitatedNetwork
import AFTD.Kb.Tcs.UnicastSessions
import AFTD.Kb.Tcs.FlowSupportsRate
import AFTD.Kb.Tcs.IsMulticommodityFlow
import AFTD.Kb.Tcs.FlowSupportsRateZero

/-!
# flow_supports_rate_mono

Topic: information   Node: a85a2cda0032

Provenance: helper lemma. folklore

If a fractional multicommodity flow on net with sessions sess supports common rate r, then for any non-negative rate r' ≤ r, rate r' is also supported.
-/

/-- Multicommodity flow rates are downward-closed. -/
theorem flow_supports_rate_mono {V : Type} [Fintype V] [DecidableEq V] {K : Type} [Fintype K] [DecidableEq K]
    (net : CapacitatedNetwork V) (sess : UnicastSessions V K) {r r' : ℝ}
    (h_supp : FlowSupportsRate net sess r) (h_nonneg : 0 ≤ r') (h_le : r' ≤ r) :
    FlowSupportsRate net sess r' := by
  by_cases hr' : r' = 0
  · subst hr'
    exact flow_supports_rate_zero net sess
  · obtain ⟨f, hf_nonneg, hf_cap, hf_div⟩ := h_supp
    have hr'_pos : 0 < r' := lt_of_le_of_ne h_nonneg (Ne.symm hr')
    have hr_pos : 0 < r := lt_of_lt_of_le hr'_pos h_le
    have hr_ne : r ≠ 0 := ne_of_gt hr_pos
    have hc_nonneg : 0 ≤ r' / r := div_nonneg h_nonneg (le_of_lt hr_pos)
    have hc_le_one : r' / r ≤ 1 := div_le_one_of_le₀ h_le (le_of_lt hr_pos)
    refine ⟨fun k u v => (r' / r) * f k u v, ?_, ?_, ?_⟩
    · intro k u v
      exact mul_nonneg hc_nonneg (hf_nonneg k u v)
    · intro u v huv
      have h_add : ∀ k, (r' / r) * f k u v + (r' / r) * f k v u = (r' / r) * (f k u v + f k v u) :=
        fun k => (mul_add (r' / r) (f k u v) (f k v u)).symm
      simp_rw [h_add]
      rw [← Finset.mul_sum]
      have hS : 0 ≤ ∑ k, (f k u v + f k v u) :=
        Finset.sum_nonneg (fun k _ => add_nonneg (hf_nonneg k u v) (hf_nonneg k v u))
      have hSC := hf_cap u v huv
      nlinarith
    · intro k v
      rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_sub]
      rw [hf_div k v]
      split_ifs with h1 h2
      · exact div_mul_cancel₀ r' hr_ne
      · rw [mul_neg, div_mul_cancel₀ r' hr_ne]
      · exact mul_zero (r' / r)
