import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicDefectiveHalfModel
import AFTD.Kb.Tcs.CyclePowerEightCorrectedCountLowerWindow
import AFTD.Kb.Tcs.CyclePowerEightCorrectedCountUpperWindow

/-!
# cycle_power_eight_zero_phase_corrected_count_periodic

Topic: combinatorics   Node: 6b4c89a276c3

Provenance: helper lemma. Corrected lower-count periodicity in the zero-phase defective half-model for RT-1 and OP-205.

In every exponent-three zero-phase defective half model, the lower-half active count plus the defect is four-periodic.
-/

theorem cycle_power_eight_zero_phase_corrected_count_periodic :
  ∀ (y : ℤ → ℕ → Bool) (e : ℤ → Bool),
    cycle_power_dyadic_defective_half_model 3 y e 0 →
    ∀ v : ℤ,
      (Finset.range 4).sum (fun a => (y (v-(a:ℤ)) a).toNat) + (e v).toNat =
      (Finset.range 4).sum (fun a => (y (v+4-(a:ℤ)) a).toNat) + (e (v+4)).toNat := by
  intro y e h v
  exact le_antisymm (cycle_power_eight_corrected_count_lower_window y e h v)
    (cycle_power_eight_corrected_count_upper_window y e h v)
