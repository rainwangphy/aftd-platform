import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicDefectiveHalfModel
import AFTD.Kb.Tcs.CyclePowerDyadicFoldModel
import AFTD.Kb.Tcs.CyclePowerDefectiveFoldCountBalance
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight

/-!
# cycle_power_dyadic_defective_fold_model_of_corrected_periodicity

Topic: combinatorics   Node: c644da49916d

Provenance: helper lemma. RT-1: use corrected-count periodicity in the defective-half-model route to the dyadic cycle-power covering problem.

For any zero-phase defective dyadic model of exponent t+1, if the lower-half active count plus the defect is 2^t-periodic, folding each class by OR of its two halves gives an ordinary tight, exactly dyadically covered, fully covered model of exponent t with t+1 active classes at every vertex. This conditional fold does not assert that defects vanish.
-/

theorem cycle_power_dyadic_defective_fold_model_of_corrected_periodicity (t : ℕ) (ht : 1 ≤ t) (x : ℤ → ℕ → Bool) (e : ℤ → Bool)
    (hm : cycle_power_dyadic_defective_half_model (t+1) x e 0)
    (hper : ∀ v : ℤ, (Finset.range (2^t)).sum (fun a => (x (v-(a:ℤ)) a).toNat) + (e v).toNat =
      (Finset.range (2^t)).sum (fun a => (x (v+(2:ℤ)^t-(a:ℤ)) a).toNat) + (e (v+(2:ℤ)^t)).toNat) :
    let y : ℤ → ℕ → Bool := fun p a => x p a || x p (a + 2^t)
    (∀ p, cycle_power_dyadic_class_weight t (y p) = (Finset.range (2^t)).sum (fun a => (y p a).toNat)) ∧
    (∀ j < t, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
      (y (v-(a:ℤ)) a && y (v-(a:ℤ)) (a+2^t-2^j)).toNat) = 1) ∧
    (∀ d : ℕ, 1 ≤ d → d < 2^t → ∀ v : ℤ,
      ∃ a : ℕ, a < 2^t-d ∧ y (v-(a:ℤ)) a = true ∧ y (v-(a:ℤ)) (a+d) = true) ∧
    (∀ v : ℤ, (Finset.range (2^t)).sum (fun a => (y (v-(a:ℤ)) a).toNat) = t+1) := by
  intro y
  rcases hm with ⟨htight, hexact, htop, hcover, hcount⟩
  have hs : (2:ℕ)^(t+1) = 2^t + 2^t := by rw [pow_succ]; omega
  refine ⟨fun p => cycle_power_dyadic_fold_tight t ht (x p) (htight p), ?_, ?_, ?_⟩
  · intro j hj v
    rw [← hexact j (by omega) v]
    refine Finset.sum_congr rfl fun a ha => ?_
    show (((x (v-(a:ℤ)) a || x (v-(a:ℤ)) (a+2^t)) &&
      (x (v-(a:ℤ)) (a+2^t-2^j) || x (v-(a:ℤ)) (a+2^t-2^j+2^t))).toNat) = _
    rw [cycle_power_dyadic_fold_pair t ht (x (v-(a:ℤ))) (htight _) j a hj (Finset.mem_range.mp ha)]
  · intro d hd1 hd2 v
    obtain ⟨a, ha, h1, h2⟩ := hcover (d + 2^t) (by omega) (by omega) (by simp; omega) v
    refine ⟨a, by omega, ?_, ?_⟩
    · simp [y, h1]
    · have heq : a + (d + 2^t) = a + d + 2^t := by ring
      rw [heq] at h2
      simp [y, h2]
  · intro v
    have hc : ∀ v : ℤ, (Finset.range (2^t+2^t)).sum (fun a => (x (v-(a:ℤ)) a).toNat) + (e v).toNat = (t+1)+1 := by
      intro v
      simpa only [← hs] using hcount v
    have hp : ∀ v : ℤ, (Finset.range (2^t)).sum (fun a =>
        (x (v-(a:ℤ)) a && x (v-(a:ℤ)) (a+2^t)).toNat) + (e (v+0)).toNat = 1 := by
      intro v
      have hh := htop v
      have hx : 2^(t+1-1) = 2^t := by congr 1 <;> omega
      rw [hx] at hh
      have heq (a : ℕ) : a + 2^(t+1) - 2^t = a + 2^t := by rw [hs, ← Nat.add_assoc, Nat.add_sub_cancel]
      simpa only [heq] using hh
    have hb := cycle_power_defective_fold_count_balance (2^t) (t+1) x e 0 hc hp v
    have per := hper v
    simp only [Nat.cast_pow, Nat.cast_ofNat, add_zero] at hb
    change (Finset.range (2^t)).sum (fun a => (x (v-(a:ℤ)) a || x (v-(a:ℤ)) (a+2^t)).toNat) = t+1
    omega
