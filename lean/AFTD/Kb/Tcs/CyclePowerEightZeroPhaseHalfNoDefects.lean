import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicDefectiveHalfModel
import AFTD.Kb.Tcs.CyclePowerEightDefectiveBoundaryPeriodTwo
import AFTD.Kb.Tcs.CyclePowerEightDefectiveBoundaryNotConstant
import AFTD.Kb.Tcs.CyclePowerEightAlternatingTruePhaseNoDefect
import AFTD.Kb.Tcs.CyclePowerEightAlternatingFalsePhaseNoDefect

/-!
# cycle_power_eight_zero_phase_half_no_defects

Topic: combinatorics   Node: e5d303dbbc3a

Provenance: helper lemma. RT-1 / OP-205, arXiv:2610.15635; finite computations 29006, 29007 and 29023.

Every zero-phase defective exponent-three model has no defects.
-/

theorem cycle_power_eight_zero_phase_half_no_defects (x : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (hm : cycle_power_dyadic_defective_half_model 3 x e 0) : ∀ p : ℤ, e p = false := by
  have hper := cycle_power_eight_defective_boundary_period_two x e hm
  have hnc := cycle_power_eight_defective_boundary_not_constant x e hm
  have halt : ∀ p : ℤ, x (p + 1) 1 = !(x p 1) := by
    by_contra hne
    obtain ⟨p, hp⟩ := not_forall.mp hne
    have heq : x (p + 1) 1 = x p 1 := by
      revert hp
      cases x (p + 1) 1 <;> cases x p 1 <;> decide
    have hk : ∀ k : ℤ, x (p + 2 * k) 1 = x p 1 ∧ x (p + 1 + 2 * k) 1 = x p 1 := by
      intro k
      induction k using Int.induction_on with
      | zero => simpa using heq
      | succ k ih =>
        have h1 := hper (p + 2 * (k + 1))
        have h2 := hper (p + 1 + 2 * (k + 1))
        have e1 : p + 2 * (k + 1) - 2 = p + 2 * k := by ring
        have e2 : p + 1 + 2 * (k + 1) - 2 = p + 1 + 2 * k := by ring
        rw [e1] at h1; rw [e2] at h2
        exact ⟨h1.trans ih.1, h2.trans ih.2⟩
      | pred k ih =>
        have h1 := hper (p + 2 * (-(k : ℤ)))
        have h2 := hper (p + 1 + 2 * (-(k : ℤ)))
        have e1 : p + 2 * (-(k : ℤ)) - 2 = p + 2 * (-(k : ℤ) - 1) := by ring
        have e2 : p + 1 + 2 * (-(k : ℤ)) - 2 = p + 1 + 2 * (-(k : ℤ) - 1) := by ring
        rw [e1] at h1; rw [e2] at h2
        exact ⟨h1.symm.trans ih.1, h2.symm.trans ih.2⟩
    have hall : ∀ q : ℤ, x q 1 = x p 1 := by
      intro q
      obtain ⟨k, hk'⟩ := Int.even_or_odd' (q - p)
      rcases hk' with hk' | hk'
      · have : q = p + 2 * k := by omega
        rw [this]; exact (hk k).1
      · have : q = p + 1 + 2 * k := by omega
        rw [this]; exact (hk k).2
    cases hpv : x p 1
    · exact hnc.1 (fun q => (hall q).trans hpv)
    · exact hnc.2 (fun q => (hall q).trans hpv)
  intro p
  cases hb : x p 1
  · exact cycle_power_eight_alternating_false_phase_no_defect x e hm halt p hb
  · exact cycle_power_eight_alternating_true_phase_no_defect x e hm halt p hb
