import AFTD.Prelude
import AFTD.Kb.Tcs.OneSlotCodeOfScaledCapacities
import AFTD.Kb.Tcs.FlowSupportsRateScaledCapacities
import AFTD.Kb.Tcs.LinearCodeSupportsRate
import AFTD.Kb.Tcs.FlowSupportsRate
import AFTD.Kb.Tcs.CausalLinearNetworkCode
import AFTD.Kb.Tcs.CapacitatedNetwork
import AFTD.Kb.Tcs.UnicastSessions

/-!
# single_slot_advantage_of_multislot_advantage

Topic: information   Node: 3bb4c974c003

Provenance: helper lemma. step towards single_slot_binary_linear_coding_advantage

Any multi-slot coding advantage yields a one-slot coding advantage: if on some instance the code rate strictly exceeds every supported fractional multicommodity flow rate, then on the same instance with all capacities multiplied by the code's horizon T there is a one-slot (T = 1) code with the same message dimension L whose rate L strictly exceeds every supported flow rate.
-/

/-- The T-scaling normalisation: a multi-slot coding advantage gives a one-slot coding advantage on T-scaled capacities. -/
theorem single_slot_advantage_of_multislot_advantage
    (h : ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
        (K : Type) (_ : Fintype K) (_ : DecidableEq K)
        (net : CapacitatedNetwork V) (sess : UnicastSessions V K) (r : ℝ),
        LinearCodeSupportsRate (ZMod 2) net sess r ∧
        ∀ r_flow, FlowSupportsRate net sess r_flow → r_flow < r) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (K : Type) (_ : Fintype K) (_ : DecidableEq K)
      (net : CapacitatedNetwork V) (sess : UnicastSessions V K)
      (code : CausalLinearNetworkCode V K (ZMod 2) net sess),
      code.T = 1 ∧ ∀ r_flow, FlowSupportsRate net sess r_flow → r_flow < (code.L : ℝ) := by
  obtain ⟨V, hV, hVd, K, hK, hKd, net, sess, r, hcs, hadv⟩ := h
  simp only [LinearCodeSupportsRate] at hcs
  obtain ⟨code, hcode⟩ := hcs
  obtain ⟨net', code', hcap, hT1, hL⟩ :=
    @one_slot_code_of_scaled_capacities V hV hVd K hK hKd
      (ZMod 2) (@ZMod.instField 2 Nat.fact_prime_two) net sess code
  refine ⟨V, hV, hVd, K, hK, hKd, net', sess, code', hT1, ?_⟩
  intro r_flow hf
  rw [hL]
  set r₀ : ℝ := r_flow / (code.T : ℝ) with hr₀def
  have hTpos : (0:ℝ) < (code.T : ℝ) := by exact_mod_cast code.hT
  have hmul : (code.T : ℝ) * r₀ = r_flow := by
    rw [hr₀def]
    field_simp
  have hflow0 : @FlowSupportsRate V hV hVd K hK hKd net' sess ((code.T : ℝ) * r₀) := by
    rw [hmul]
    exact hf
  have hFlow0 : @FlowSupportsRate V hV hVd K hK hKd net sess r₀ :=
    (@flow_supports_rate_scaled_capacities V hV hVd K hK hKd net sess code.T code.hT r₀).mp
      ⟨net', hcap, hflow0⟩
  have hrlt : r₀ < (code.L : ℝ) / (code.T : ℝ) := lt_of_lt_of_le (hadv r₀ hFlow0) hcode
  have hmain : r₀ * (code.T : ℝ) < (code.L : ℝ) := by
    calc r₀ * (code.T : ℝ) < ((code.L : ℝ) / (code.T : ℝ)) * (code.T : ℝ) :=
          mul_lt_mul_of_pos_right hrlt hTpos
      _ = (code.L : ℝ) := by field_simp
  have hrfl : r_flow = r₀ * (code.T : ℝ) := by rw [← hmul]; ring
  rw [hrfl]
  exact hmain
