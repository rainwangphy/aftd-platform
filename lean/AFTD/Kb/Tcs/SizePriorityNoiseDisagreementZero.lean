import AFTD.Prelude
import AFTD.Kb.Tcs.SizePriorityNoiseDisagreement
import AFTD.Kb.Tcs.SizePriorityMatching

/-!
# size_priority_noise_disagreement_zero

Topic: graphs   Node: d899e0f20700

Provenance: helper lemma. Sanity lemma for size_priority_noise_disagreement (OP-1789).

With resampling probability p = 0 nothing is resampled, so D_n(c,0) = 0 for every n and c.
-/

theorem size_priority_noise_disagreement_zero (n : ℕ) (c : ℝ) :
    size_priority_noise_disagreement n c 0 = 0 := by
  unfold size_priority_noise_disagreement
  apply Finset.sum_eq_zero
  intro E _
  rw [Finset.sum_eq_single (∅ : Finset (Fin n × Fin n))]
  · simp
  · intro R _ hR
    have : R.card ≠ 0 := by simpa using hR
    simp [zero_pow this]
  · simp
