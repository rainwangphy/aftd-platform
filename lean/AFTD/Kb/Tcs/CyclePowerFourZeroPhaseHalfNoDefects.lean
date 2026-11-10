import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicDefectiveHalfModel
import AFTD.Kb.Tcs.CyclePowerFourZeroDefectLocalCore
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight

/-!
# cycle_power_four_zero_phase_half_no_defects

Topic: combinatorics   Node: 80c2d0d0bffe

Provenance: helper lemma. Defective half-model reduction for research thread RT-1.

Every exponent-two zero-phase defective half model has no defects.
-/

theorem cycle_power_four_zero_phase_half_no_defects
    (y : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (hm : cycle_power_dyadic_defective_half_model 2 y e 0) : ∀ v, e v = false := by
  rcases hm with ⟨htight, hexact, htop, hcover, hcount⟩
  have hend (p : ℤ) : y p 0 = true ∧ y p 3 = true := by
    have h := hexact 0 (by omega) p
    norm_num [Finset.sum_range_succ] at h
    cases h0 : y p 0 <;> cases h3 : y p 3 <;> simp_all
  apply cycle_power_four_zero_defect_local_core (fun p => y p 1) (fun p => y p 2) e
  · intro v
    have h := htop v
    norm_num [Finset.sum_range_succ, hend] at h
    simpa using h
  · intro v
    have h := hcount v
    norm_num [Finset.sum_range_succ, hend] at h
    omega
  · intro v
    obtain ⟨a, ha, h1, h2⟩ := hcover 1 (by norm_num) (by norm_num) (by norm_num) v
    have ha' : a < 3 := by norm_num at ha ⊢; omega
    interval_cases a
    · left; simpa using h2
    · right; left; exact ⟨by simpa using h1, by simpa using h2⟩
    · right; right; simpa using h1
