import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicDefectiveHalfModel
import AFTD.Kb.Tcs.CyclePowerFourCorrectedCountPeriodicOfCount
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight

/-!
# cycle_power_four_zero_phase_corrected_count_periodic

Topic: combinatorics   Node: 1267cf310f00

Provenance: helper lemma. Corrected lower-count periodicity in the zero-phase defective half-model for RT-1 and OP-205.

In every exponent-two zero-phase defective half model, the lower-half active count plus the defect is two-periodic.
-/

theorem cycle_power_four_zero_phase_corrected_count_periodic
    (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (hm : cycle_power_dyadic_defective_half_model 2 y e 0) :
    ∀ v : ℤ,
      (Finset.range 2).sum (fun a => (y (v-(a:ℤ)) a).toNat) + (e v).toNat =
      (Finset.range 2).sum (fun a => (y (v+2-(a:ℤ)) a).toNat) + (e (v+2)).toNat := by
  rcases hm with ⟨_, hexact, htop, _, hcount⟩
  have hend (p : ℤ) : y p 0 = true ∧ y p 3 = true := by
    have h := hexact 0 (by omega) p
    norm_num [Finset.sum_range_succ] at h
    cases h0 : y p 0 <;> cases h3 : y p 3 <;> simp_all
  apply cycle_power_four_corrected_count_periodic_of_count y e hend
  · intro v
    simpa using htop v
  · intro v
    simpa using hcount v
