import AFTD.Prelude
import AFTD.Kb.Tcs.FlowSupportsRate
import AFTD.Kb.Tcs.IsMulticommodityFlow
import AFTD.Kb.Tcs.CapacitatedNetwork
import AFTD.Kb.Tcs.UnicastSessions

/-!
# flow_supports_rate_scaled_capacities

Topic: information   Node: 7b4f7db3667c

Provenance: helper lemma. step towards single_slot_binary_linear_coding_advantage

Fractional multicommodity flow feasibility is homogeneous of degree one in (flow, rate, capacities): for T > 0, a flow of common rate T*r on the network with capacities T * cap is the same object as a flow of rate r on the network with capacities cap (multiply the flow by T in one direction, divide by it in the other). Both the capacity inequalities and the conservation equations are linear, which is the whole content.
-/

/-- Flow feasibility is homogeneous of degree one: rate T*r on capacities T * cap is rate r on capacities cap. -/
theorem flow_supports_rate_scaled_capacities
    {V : Type} [Fintype V] [DecidableEq V] {K : Type} [Fintype K] [DecidableEq K]
    (net : CapacitatedNetwork V) (sess : UnicastSessions V K) {T : ℕ} (hT : 0 < T) (r : ℝ) :
    (∃ net' : CapacitatedNetwork V, (∀ e : Sym2 V, net'.cap e = (T : ℝ) * net.cap e) ∧
        FlowSupportsRate net' sess ((T : ℝ) * r)) ↔ FlowSupportsRate net sess r := by
  have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hTne : (T : ℝ) ≠ 0 := ne_of_gt hTpos
  constructor
  · rintro ⟨net', hcap, f, h1, h2, h3⟩
    refine ⟨fun k u v => f k u v / (T : ℝ), ?_, ?_, ?_⟩
    · intro k u v
      exact div_nonneg (h1 k u v) (le_of_lt hTpos)
    · intro u v huv
      have e1 : ∑ k, (f k u v / (T:ℝ) + f k v u / (T:ℝ))
          = (∑ k, (f k u v + f k v u)) / (T:ℝ) := by
        have step1 : ∑ k, (f k u v / (T:ℝ) + f k v u / (T:ℝ))
            = ∑ k, ((f k u v + f k v u) / (T:ℝ)) := by
          apply Finset.sum_congr rfl; intro k _; rw [← add_div]
        rw [step1, ← Finset.sum_div]
      rw [e1, div_le_iff₀ hTpos]
      calc ∑ k, (f k u v + f k v u) ≤ net'.cap s(u,v) := h2 u v huv
        _ = (T:ℝ) * net.cap s(u,v) := hcap s(u,v)
        _ = net.cap s(u,v) * (T:ℝ) := by ring
    · intro k v
      have e1 : ∑ w, f k v w / (T:ℝ) = (∑ w, f k v w) / (T:ℝ) := by rw [Finset.sum_div]
      have e2 : ∑ u, f k u v / (T:ℝ) = (∑ u, f k u v) / (T:ℝ) := by rw [Finset.sum_div]
      rw [e1, e2, ← sub_div, h3 k v]
      split_ifs with hv1 hv2
      · rw [div_eq_iff hTne]; ring
      · rw [div_eq_iff hTne]; ring
      · simp
  · rintro ⟨g, h1, h2, h3⟩
    let net' : CapacitatedNetwork V :=
      { G := net.G
        decAdj := net.decAdj
        cap := fun e => (T:ℝ) * net.cap e
        cap_pos := by intro e he; exact mul_pos hTpos (net.cap_pos e he)
        cap_zero := by intro e he; rw [net.cap_zero e he, mul_zero] }
    refine ⟨net', ?_, ?_⟩
    · intro e; rfl
    · refine ⟨fun k u v => (T:ℝ) * g k u v, ?_, ?_, ?_⟩
      · intro k u v
        exact mul_nonneg (le_of_lt hTpos) (h1 k u v)
      · intro u v huv
        have hcap' : net'.cap s(u,v) = (T:ℝ) * net.cap s(u,v) := rfl
        rw [hcap']
        have e1 : ∑ k, ((T:ℝ) * g k u v + (T:ℝ) * g k v u)
            = (T:ℝ) * ∑ k, (g k u v + g k v u) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro k _; ring
        rw [e1]
        exact mul_le_mul_of_nonneg_left (h2 u v huv) (le_of_lt hTpos)
      · intro k v
        have e1 : ∑ w, (T:ℝ) * g k v w = (T:ℝ) * ∑ w, g k v w := by rw [Finset.mul_sum]
        have e2 : ∑ u, (T:ℝ) * g k u v = (T:ℝ) * ∑ u, g k u v := by rw [Finset.mul_sum]
        rw [e1, e2, ← mul_sub, h3 k v]
        split_ifs <;> ring
