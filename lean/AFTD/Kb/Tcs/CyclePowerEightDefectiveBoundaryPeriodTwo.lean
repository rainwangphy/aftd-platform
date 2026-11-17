import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicDefectiveHalfModel
import AFTD.Kb.Tcs.CyclePowerEightZeroPhaseCorrectedCountPeriodic
import AFTD.Kb.Tcs.CyclePowerDyadicDefectiveFoldModelOfCorrectedPeriodicity
import AFTD.Kb.Tcs.CyclePowerDyadicFoldModel
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.Bit

/-!
# cycle_power_eight_defective_boundary_period_two

Topic: combinatorics   Node: 9841a5d1989e

Provenance: helper lemma. RT-1 / OP-205, arXiv:2610.15635; finite computations 29006, 29007 and 29023.

The first inner class bit of every zero-phase defective exponent-three model is two-periodic.
-/

namespace RT1Fold939
theorem rt1_eight_defective_fold (x : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (hm : cycle_power_dyadic_defective_half_model 3 x e 0) :
    let y : ℤ → ℕ → Bool := fun p a => x p a || x p (a + 2^2)
    (∀ p, cycle_power_dyadic_class_weight 2 (y p) =
      (Finset.range (2^2)).sum (fun a => (y p a).toNat)) ∧
    (∀ j < 2, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
      (y (v-(a:ℤ)) a && y (v-(a:ℤ)) (a+2^2-2^j)).toNat) = 1) ∧
    (∀ d : ℕ, 1 ≤ d → d < 2^2 → ∀ v : ℤ,
      ∃ a : ℕ, a < 2^2-d ∧ y (v-(a:ℤ)) a = true ∧
        y (v-(a:ℤ)) (a+d) = true) ∧
    (∀ v : ℤ, (Finset.range (2^2)).sum (fun a =>
      (y (v-(a:ℤ)) a).toNat) = 2+1) := by
  apply cycle_power_dyadic_defective_fold_model_of_corrected_periodicity 2 (by decide) x e hm
  simpa using cycle_power_eight_zero_phase_corrected_count_periodic x e hm

/-- A four-position exact model of count three has a two-periodic first inner bit. -/
theorem rt1_folded_four_first_inner_period_two (y : ℤ → ℕ → Bool)
    (he : ∀ j < 2, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
      (y (v-(a:ℤ)) a && y (v-(a:ℤ)) (a+2^2-2^j)).toNat) = 1)
    (hc : ∀ v : ℤ, (Finset.range (2^2)).sum (fun a =>
      (y (v-(a:ℤ)) a).toNat) = 3) :
    ∀ p : ℤ, y p 1 = y (p-2) 1 := by
  have ends (p : ℤ) : y p 0 = true ∧ y p 3 = true := by
    have h := he 0 (by decide) p
    norm_num [Finset.sum_range_succ] at h
    cases h0 : y p 0 <;> cases h3 : y p 3 <;> simp_all
  have hpair (p : ℤ) : (y p 2).toNat + (y (p-1) 1).toNat = 1 := by
    have h := he 1 (by decide) p
    norm_num [Finset.sum_range_succ, ends] at h
    omega
  have hactive (p : ℤ) : (y p 1).toNat + (y (p-1) 2).toNat = 1 := by
    have h := hc (p+1)
    have h1 : p+1-1 = p := by omega
    have h2 : p+1-2 = p-1 := by omega
    norm_num [Finset.sum_range_succ, ends, h1, h2] at h
    omega
  intro p
  have h1 := hactive p
  have h2 := hpair (p-1)
  have hindex : p-1-1 = p-2 := by omega
  rw [hindex] at h2
  have heq : (y p 1).toNat = (y (p-2) 1).toNat := by omega
  cases ha : y p 1 <;> cases hb : y (p-2) 1 <;> simp_all

/-- The first inner bit is unchanged by this fold and is two-periodic. -/
theorem rt1_eight_first_inner_period_two (x : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (hm : cycle_power_dyadic_defective_half_model 3 x e 0) :
    ∀ p : ℤ, x p 1 = x (p-2) 1 := by
  have hf := rt1_eight_defective_fold x e hm
  dsimp at hf
  rcases hf with ⟨_, he, _, hc⟩
  have hper := rt1_folded_four_first_inner_period_two (fun p a => x p a || x p (a + 4)) he hc
  have unchanged (p : ℤ) : (x p 1 || x p 5) = x p 1 := by
    have hparent := (cycle_power_dyadic_fold_parents 2 (by decide) (x p) (hm.1 p)).1 1 (by decide)
    cases h1 : x p 1 <;> cases h5 : x p 5 <;> simp_all
  intro p
  simpa only [show (1 : ℕ) + 2^2 = 5 by decide, unchanged] using hper p

end RT1Fold939

theorem cycle_power_eight_defective_boundary_period_two (x : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (hm : cycle_power_dyadic_defective_half_model 3 x e 0) : ∀ p : ℤ, x p 1 = x (p - 2) 1 := by
  exact RT1Fold939.rt1_eight_first_inner_period_two x e hm
