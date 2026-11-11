import AFTD.Prelude
import AFTD.Kb.Physics.SlowModeDephasing
import AFTD.Kb.Tcs.G

/-!
# slow_mode_dephasing_zero

Topic: statistical_mechanics   Node: 859f2149dbed

Provenance: helper lemma. arXiv:2609.13387

At time s = 0, the quantum slow-mode dephasing factor kappa_{n,m}(0) equals 1 for every n >= 2 and every m.
-/

noncomputable def slow_mode_dephasing_zero_sum (n : ℕ)
    (H : Matrix (Equiv.Perm (Fin n)) (Equiv.Perm (Fin n)) ℂ) : ℝ :=
  ∑ g : Equiv.Perm (Fin n),
    ‖(NormedSpace.exp (- (Complex.I * (0 : ℂ)) • H)) g 1‖ ^ 2 *
      ((((Finset.filter (fun i : Fin n ↦ g i = i) Finset.univ).card : ℝ) - 1) / ((n : ℝ) - 1))

lemma slow_mode_dephasing_zero_exp_zero (n : ℕ)
    (H : Matrix (Equiv.Perm (Fin n)) (Equiv.Perm (Fin n)) ℂ) :
    NormedSpace.exp (- (Complex.I * (0 : ℂ)) • H) = 1 := by
  have hz : (- (Complex.I * (0 : ℂ)) : ℂ) = 0 := by simp
  rw [hz, zero_smul, NormedSpace.exp_zero]

lemma slow_mode_dephasing_zero_sum_eq_one (n : ℕ) (hn : 2 ≤ n)
    (H : Matrix (Equiv.Perm (Fin n)) (Equiv.Perm (Fin n)) ℂ) :
    slow_mode_dephasing_zero_sum n H = 1 := by
  dsimp [slow_mode_dephasing_zero_sum]
  rw [slow_mode_dephasing_zero_exp_zero]
  rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
  · rw [Matrix.one_apply, if_pos rfl]
    have hfilt : ((Finset.filter (fun i : Fin n ↦ (1 : Equiv.Perm (Fin n)) i = i) Finset.univ).card : ℝ) = (n : ℝ) := by
      simp
    rw [hfilt]
    have hne : (n : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
      linarith
    simp [div_self hne]
  · intro b _ hb
    rw [Matrix.one_apply, if_neg hb]
    simp
  · intro h
    exact (h (Finset.mem_univ 1)).elim

/-- At time s = 0, the slow-mode dephasing factor kappa_{n,m}(0) equals 1. -/
theorem slow_mode_dephasing_zero (n m : ℕ) (hn : 2 ≤ n) :
    slow_mode_dephasing n m 0 = 1 := by
  exact slow_mode_dephasing_zero_sum_eq_one n hn _
