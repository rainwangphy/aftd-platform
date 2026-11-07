import AFTD.Prelude
import AFTD.Kb.Tcs.DiscreteMemorylessChannel
import AFTD.Kb.Tcs.ChannelDistinguishabilityGraph
import AFTD.Kb.Tcs.RandomSwitchingChannel
import AFTD.Kb.Tcs.ChannelZeroErrorCodeSize
import AFTD.Kb.Tcs.ChannelZeroErrorRate
import AFTD.Kb.Tcs.RandomSwitchingDistinguishabilityGraph
import AFTD.Kb.Tcs.SimpleGraphCategoricalProd
import AFTD.Kb.Tcs.SimpleGraphOrPower
import AFTD.Kb.Tcs.ShannonOrCapacity

/-!
# proposition_5_1_random_switching_channel_realization

Topic: information   Node: 6ee28d163ffb

Provenance: formalization of a published result. Source: arXiv:2610.41977 Proposition 5.1 -- Hedetniemi's conjecture for Shannon OR-capacity: counterexamples and asymptotic separation

For any discrete memoryless channels W_G and W_H and any switching probability p ∈ (0, 1), the distinguishability graph of the switched channel W_sw is the categorical product D(W_G) × D(W_H), the maximum number of zero-error messages in n uses is M_0(W_sw, n) = omega((D(W_G) × D(W_H))^{∨n}), and the zero-error capacity rate is R_0(W_sw) = log_2 C_OR(D(W_G) × D(W_H)), with both quantities independent of p.
-/

/-- Proposition 5.1: Random switching realizes the categorical product of distinguishability graphs, with block-code sizes and rate independent of p. -/
theorem proposition_5_1_random_switching_channel_realization
    {A B Y Z : Type*} [Fintype Y] [Fintype Z]
    (W_G : DiscreteMemorylessChannel A Y) (W_H : DiscreteMemorylessChannel B Z)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    channel_distinguishability_graph (random_switching_channel W_G W_H p hp0 hp1) =
      simple_graph_categorical_prod (channel_distinguishability_graph W_G)
        (channel_distinguishability_graph W_H) ∧
    (∀ n : ℕ, channel_zero_error_code_size (random_switching_channel W_G W_H p hp0 hp1) n =
      (simple_graph_or_power (simple_graph_categorical_prod
        (channel_distinguishability_graph W_G) (channel_distinguishability_graph W_H)) n).cliqueNum) ∧
    channel_zero_error_rate (random_switching_channel W_G W_H p hp0 hp1) =
      Real.logb 2 (shannon_or_capacity (simple_graph_categorical_prod
        (channel_distinguishability_graph W_G) (channel_distinguishability_graph W_H))) := by
  refine ⟨random_switching_distinguishability_graph W_G W_H p hp0 hp1, ?_, ?_⟩
  · intro n
    rw [channel_zero_error_code_size, random_switching_distinguishability_graph]
  · rw [channel_zero_error_rate, random_switching_distinguishability_graph]
