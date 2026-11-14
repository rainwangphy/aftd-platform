import AFTD.Prelude
import AFTD.Kb.Physics.EnergyFilterStepSumIntegral

/-!
# energy_filter_step_sum_eq_floor

Topic: statistical_mechanics   Node: a34e46797a6a

Provenance: helper lemma. OP-892: centered binomial fourth-mass asymptotic via rescaled step functions and dominated convergence.

If a real function on the integers vanishes outside a finite set, then the corresponding finite sum of interval indicators of width 1/h at real x equals the function at floor(hx), for h>0.
-/

theorem energy_filter_step_sum_eq_floor
    (s : Finset ℤ) (w : ℤ → ℝ) (h x : ℝ) (hh : 0 < h)
    (hw : ∀ i ∉ s, w i = 0) :
    (∑ i ∈ s, (Set.Ico ((i:ℝ)/h) (((i:ℝ)+1)/h)).indicator (fun _ : ℝ => w i) x) =
      w (Int.floor (h*x)) := by
  classical
  have hiff (i : ℤ) : x ∈ Set.Ico ((i:ℝ)/h) (((i:ℝ)+1)/h) ↔ Int.floor (h*x) = i := by
    rw [Set.mem_Ico, Int.floor_eq_iff]
    constructor
    · rintro ⟨ha,hb⟩
      constructor
      · simpa [mul_comm] using (div_le_iff₀ hh).mp ha
      · simpa [mul_comm] using (lt_div_iff₀ hh).mp hb
    · rintro ⟨ha,hb⟩
      constructor
      · apply (div_le_iff₀ hh).mpr
        simpa [mul_comm] using ha
      · apply (lt_div_iff₀ hh).mpr
        simpa [mul_comm] using hb
  by_cases hs : Int.floor (h*x) ∈ s
  · rw [Finset.sum_eq_single (Int.floor (h*x))]
    · exact Set.indicator_of_mem ((hiff _).2 rfl) _
    · intro b hb hne
      apply Set.indicator_of_notMem
      intro hx
      exact hne ((hiff b).1 hx).symm
    · intro hn
      exact (hn hs).elim
  · rw [hw _ hs]
    apply Finset.sum_eq_zero
    intro b hb
    apply Set.indicator_of_notMem
    intro hx
    have heq := (hiff b).1 hx
    apply hs
    rw [heq]
    exact hb
