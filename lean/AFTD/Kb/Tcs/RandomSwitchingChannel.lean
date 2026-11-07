import AFTD.Prelude
import AFTD.Kb.Tcs.DiscreteMemorylessChannel

/-!
# random_switching_channel

Topic: information   Node: e3bc60606e4a

Provenance: formalization of a published result. Source: arXiv:2610.41977, Section 5

Given channels W_G and W_H and switching parameter p ∈ (0, 1), the random switching channel has input pairs (a, b) and tagged outputs in Y ⊕ Z with transition probabilities p * W_G(y|a) and (1-p) * W_H(z|b).
-/

/-- The random switching channel between two discrete memoryless channels with switching parameter p in (0, 1). -/
def random_switching_channel {A B Y Z : Type*} [Fintype Y] [Fintype Z]
    (W_G : DiscreteMemorylessChannel A Y) (W_H : DiscreteMemorylessChannel B Z)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    DiscreteMemorylessChannel (A × B) (Sum Y Z) where
  prob := fun ab => fun
    | Sum.inl y => p * W_G.prob ab.1 y
    | Sum.inr z => (1 - p) * W_H.prob ab.2 z
  prob_nonneg := by
    rintro ⟨a, b⟩ (y | z)
    · exact mul_nonneg hp0.le (W_G.prob_nonneg a y)
    · exact mul_nonneg (sub_nonneg.mpr hp1.le) (W_H.prob_nonneg b z)
  prob_sum := by
    rintro ⟨a, b⟩
    rw [Fintype.sum_sum_type]
    simp_rw [← Finset.mul_sum]
    rw [W_G.prob_sum a, W_H.prob_sum b, mul_one, mul_one]
    linarith
