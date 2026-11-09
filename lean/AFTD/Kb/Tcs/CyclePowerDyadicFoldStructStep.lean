import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicFoldModel
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight

/-!
# cycle_power_dyadic_fold_struct_step

Topic: combinatorics   Node: 3344e06804e1

Provenance: helper lemma. RT-1 / OP-205 (arXiv:2610.15635, Theorems 1.3-1.4: eq(C_n^k) for k+1 = 2^m, n even, (k+1) not dividing n). Session 2026-11-09: folding offsets modulo 2^t (experiment 19407).

Induction step through the fold. If every model at exponent t (t ≥ 2) has alternating bit 1 and endpoint-only classes without bit 1, then so does a model at exponent t+1 provided its left count is 2^t-periodic and its two middle bits 2^t-1, 2^t vanish in classes without bit 1 (the latter may assume alternation and the vanishing of all other inner bits).
-/

theorem cycle_power_dyadic_fold_struct_step (t : ℕ) (ht : 2 ≤ t)
    (ih : ∀ (y : ℤ → ℕ → Bool),
      (∀ p, cycle_power_dyadic_class_weight t (y p) =
        (Finset.range (2^t)).sum (fun a => (y p a).toNat)) →
      (∀ j < t, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
        (y (v-(a : ℤ)) a && y (v-(a : ℤ)) (a+2^t-2^j)).toNat) = 1) →
      (∀ d : ℕ, 1 ≤ d → d < 2^t → ∀ v : ℤ,
        ∃ a : ℕ, a < 2^t-d ∧ y (v-(a : ℤ)) a = true ∧
          y (v-(a : ℤ)) (a+d) = true) →
      (∀ v : ℤ, (Finset.range (2^t)).sum (fun a =>
        (y (v-(a : ℤ)) a).toNat) = t+1) →
      (∀ p : ℤ, y (p+1) 1 = !y p 1) ∧
      (∀ p : ℤ, y p 1 = false → ∀ j, 0 < j → j < 2^t - 1 → y p j = false))
    (x : ℤ → ℕ → Bool)
    (htight : ∀ p, cycle_power_dyadic_class_weight (t+1) (x p) =
      (Finset.range (2^(t+1))).sum (fun a => (x p a).toNat))
    (hexact : ∀ j < t+1, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(t+1)-2^j)).toNat) = 1)
    (hcover : ∀ d : ℕ, 1 ≤ d → d < 2^(t+1) → ∀ v : ℤ,
      ∃ a : ℕ, a < 2^(t+1)-d ∧ x (v-(a : ℤ)) a = true ∧
        x (v-(a : ℤ)) (a+d) = true)
    (hcount : ∀ v : ℤ, (Finset.range (2^(t+1))).sum (fun a =>
      (x (v-(a : ℤ)) a).toNat) = (t+1)+1)
    (hfold : ∀ v : ℤ, (Finset.range (2^t)).sum (fun a => (x (v-(a : ℤ)) a).toNat) =
      (Finset.range (2^t)).sum (fun a => (x (v+(2:ℤ)^t-(a : ℤ)) a).toNat))
    (hmid : (∀ p : ℤ, x (p+1) 1 = !x p 1) →
      (∀ p : ℤ, x p 1 = false → ∀ j, 0 < j → j < 2^(t+1) - 1 → j ≠ 2^t - 1 → j ≠ 2^t →
        x p j = false) →
      ∀ p : ℤ, x p 1 = false → x p (2^t - 1) = false ∧ x p (2^t) = false) :
    (∀ p : ℤ, x (p+1) 1 = !x p 1) ∧
    (∀ p : ℤ, x p 1 = false → ∀ j, 0 < j → j < 2^(t+1) - 1 → x p j = false) := by
  have ht1 : 1 ≤ t := by omega
  obtain ⟨yt, yex, ycv, ycn⟩ :=
    cycle_power_dyadic_fold_model t ht1 x htight hexact hcover hcount hfold
  obtain ⟨yalt, yend⟩ := ih (fun p a => x p a || x p (a + 2^t)) yt yex ycv ycn
  have hQ : 2 ≤ 2^(t-1) := by
    calc 2 = 2^1 := by norm_num
      _ ≤ 2^(t-1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2t : (2:ℕ)^t = 2 * 2^(t-1) := by rw [← pow_succ']; congr 1; omega
  have hs : (2:ℕ)^(t+1) = 2 * 2^t := by rw [pow_succ']
  have hone : ∀ p : ℤ, (x p 1 || x p (1 + 2^t)) = x p 1 := by
    intro p
    have h3 := (cycle_power_dyadic_fold_parents t ht1 (x p) (htight p)).1 1 (by omega)
    revert h3
    generalize x p (1 + 2^t) = u
    generalize x p 1 = w
    cases w <;> cases u <;> simp
  have halt : ∀ p : ℤ, x (p+1) 1 = !x p 1 := by
    intro p
    have h := yalt p
    simp only [hone] at h
    exact h
  have hpart : ∀ p : ℤ, x p 1 = false → ∀ j, 0 < j → j < 2^(t+1) - 1 → j ≠ 2^t - 1 → j ≠ 2^t →
      x p j = false := by
    intro p hp j hj1 hj2 hj3 hj4
    have hy1 : (x p 1 || x p (1 + 2^t)) = false := by rw [hone]; exact hp
    rcases lt_or_gt_of_ne hj4 with h | h
    · have h5 := yend p hy1 j hj1 (by omega)
      simp only [Bool.or_eq_false_iff] at h5
      exact h5.1
    · have h5 := yend p hy1 (j - 2^t) (by omega) (by omega)
      simp only [Bool.or_eq_false_iff] at h5
      rw [show j - 2^t + 2^t = j by omega] at h5
      exact h5.2
  refine ⟨halt, ?_⟩
  intro p hp j hj1 hj2
  by_cases hj3 : j = 2^t - 1
  · rw [hj3]; exact (hmid halt hpart p hp).1
  by_cases hj4 : j = 2^t
  · rw [hj4]; exact (hmid halt hpart p hp).2
  exact hpart p hp j hj1 hj2 hj3 hj4
