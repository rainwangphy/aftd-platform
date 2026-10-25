import AFTD.Prelude
import AFTD.Kb.Tcs.EvalNetwork
import AFTD.Kb.Tcs.ReluNetworkHasUnitIntervalZero
import AFTD.Kb.Tcs.ReluNetworkEvalContinuous
import AFTD.Kb.Tcs.ReLUNetwork

/-!
# relu_network_zero_of_ivt

Topic: np_completeness   Node: 08259fb98ddd

Provenance: helper lemma. folklore

If a feedforward ReLU neural network of width $k$ evaluates to a non-positive value at 0 and a non-negative value at 1, then by the intermediate value theorem it has a zero in the unit interval $[0, 1]$.
-/

/-- Zero existence via the intermediate value theorem for ReLU networks. -/
theorem relu_network_zero_of_ivt {k : ℕ} (net : ReLUNetwork k)
  (h0 : evalNetwork net 0 ≤ 0) (h1 : 0 ≤ evalNetwork net 1) :
  relu_network_has_unit_interval_zero net := by
  unfold relu_network_has_unit_interval_zero
  have hcont : ContinuousOn (evalNetwork net) (Set.Icc (0:ℝ) 1) :=
    (relu_network_eval_continuous net).continuousOn
  have hmem : (0:ℝ) ∈ Set.Icc (evalNetwork net 0) (evalNetwork net 1) := ⟨h0, h1⟩
  have himg := intermediate_value_Icc (show (0:ℝ) ≤ 1 by norm_num) hcont hmem
  obtain ⟨x, hx, hfx⟩ := himg
  exact ⟨x, hx, hfx⟩
