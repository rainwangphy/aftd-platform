import AFTD.Prelude
import AFTD.Kb.Tcs.CausalLinearNetworkCode
import AFTD.Kb.Tcs.CapacitatedNetwork
import AFTD.Kb.Tcs.UnicastSessions

/-!
# one_slot_code_of_scaled_capacities

Topic: information   Node: 9db68395e279

Provenance: helper lemma. step towards single_slot_binary_linear_coding_advantage

A deterministic causal linear code with T transmission slots on a capacitated network can be read as a one-slot (T = 1) code with the same message dimension L on the network whose capacities are all multiplied by T: the capacity condition of the one-slot code on T * cap is literally the T-slot capacity condition on cap, and every other field (transmission list, encoding, decoding, causality, locality, correctness) is copied unchanged.
-/

/-- Normalisation: a T-slot code on capacities cap becomes a one-slot code with the same message dimension on capacities T * cap. -/
theorem one_slot_code_of_scaled_capacities
    {V : Type} [Fintype V] [DecidableEq V] {K : Type} [Fintype K] [DecidableEq K]
    (F : Type) [Field F] (net : CapacitatedNetwork V) (sess : UnicastSessions V K)
    (code : CausalLinearNetworkCode V K F net sess) :
    ∃ (net' : CapacitatedNetwork V) (code' : CausalLinearNetworkCode V K F net' sess),
      (∀ e : Sym2 V, net'.cap e = (code.T : ℝ) * net.cap e) ∧ code'.T = 1 ∧ code'.L = code.L := by
  have hT : (0 : ℝ) < (code.T : ℝ) := by exact_mod_cast code.hT
  let net' : CapacitatedNetwork V :=
    { G := net.G, decAdj := net.decAdj, cap := fun e => (code.T : ℝ) * net.cap e,
      cap_pos := fun e he => mul_pos hT (net.cap_pos e he),
      cap_zero := fun e he => by rw [net.cap_zero e he, mul_zero] }
  let code' : CausalLinearNetworkCode V K F net' sess :=
    { M := code.M, T := 1, L := code.L, hT := by norm_num, hL := code.hL,
      snd := code.snd, rcv := code.rcv, snd_ne_rcv := code.snd_ne_rcv,
      cap_le := fun e => by
        have h := code.cap_le e
        simp only [net']
        simpa using h,
      α := code.α, β := code.β, γ := code.γ,
      causal := code.causal, snd_local := code.snd_local,
      rcv_local := code.rcv_local, dec_local := code.dec_local,
      correct := code.correct }
  exact ⟨net', code', fun e => rfl, rfl, rfl⟩
