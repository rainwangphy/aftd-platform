import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.FiniteEnvyCycleImprovement

/-!
# finite_column_switch_improvement

Topic: fair_division   Node: 5b593e9d6394

Provenance: helper lemma. Structural helper for efx_four_agents_additive_exists (OP-7), campaign IN-404, 2026-11-01.

In a finite nonempty real matrix w, suppose each column other than s is strictly envied relative to diagonal values, and some agent other than s strictly prefers replacement value c(i) to her diagonal. Then either a permutation of the original columns or a permutation after replacing column s by c weakly improves all diagonal values and strictly improves one.
-/

open Function Finset

theorem finite_column_switch_improvement {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α]
    (w : α → α → ℝ) (s : α) (c : α → ℝ)
    (hother : ∀ j, j ≠ s → ∃ i, w i i < w i j)
    (hc : ∃ i, i ≠ s ∧ w i i < c i) :
    (∃ p : Equiv.Perm α, (∀ i, w i i ≤ w i (p i)) ∧ ∃ i, w i i < w i (p i)) ∨
    (∃ p : Equiv.Perm α,
      (∀ i, w i i ≤ if p i = s then c i else w i (p i)) ∧
        ∃ i, w i i < if p i = s then c i else w i (p i)) := by
  classical
  let v : α → α → ℝ := fun i j => if i = s then w i j else if j = s then c i else w i j
  have hd (i : α) : v i i = w i i := by by_cases hi : i = s <;> simp [v, hi]
  have he (j : α) : ∃ i, v i i < v i j := by
    by_cases hj : j = s
    · obtain ⟨i, hi, hic⟩ := hc
      exact ⟨i, by simpa [hd, v, hi, hj] using hic⟩
    · obtain ⟨i, hi⟩ := hother j hj
      refine ⟨i, ?_⟩
      by_cases his : i = s <;> simpa [hd, v, his, hj] using hi
  obtain ⟨p, hp, k, hk⟩ := finite_envy_cycle_improvement v he
  by_cases hps : p s = s
  · left
    have hv (i : α) : v i (p i) = w i (p i) := by
      by_cases hi : i = s
      · simp [v, hi]
      · have hpi : p i ≠ s := fun h => hi (p.injective (h.trans hps.symm))
        simp [v, hi, hpi]
    exact ⟨p, fun i => by simpa only [hd, hv] using hp i,
      k, by simpa only [hd, hv] using hk⟩
  · right
    have hv (i : α) : v i (p i) = if p i = s then c i else w i (p i) := by
      by_cases hi : i = s
      · subst i
        simp [v, hps]
      · simp [v, hi]
    exact ⟨p, fun i => by simpa only [hd, hv] using hp i,
      k, by simpa only [hd, hv] using hk⟩
