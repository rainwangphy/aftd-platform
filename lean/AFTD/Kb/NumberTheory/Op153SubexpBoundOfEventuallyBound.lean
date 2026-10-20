import AFTD.Prelude

/-!
# op_153_subexp_bound_of_eventually_bound

Topic: elementary_number_theory   Node: 8481dabf7fc7

Provenance: helper lemma. step towards op_153_subexp_bound_intersective_quadratic

If a difference-avoiding set in {1, ..., N} satisfies |A| ≤ C·N·exp(−c√(log N · log log N)) for all sufficiently large N (with constants c, C depending on h), then it satisfies the same shape of bound for *all* N ≥ 3, at the cost of enlarging C: the finitely many N below the threshold are absorbed by the trivial bound |A| ≤ N.
-/

/-- Small-N absorption: an eventual subexponential difference bound implies the same bound for every N ≥ 3, with a larger constant. -/
theorem op_153_subexp_bound_of_eventually_bound (h : Polynomial ℤ) :
    (∃ c > 0, ∃ C > 0, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A ⊆ Finset.Icc 1 N,
      (∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬ ∃ n : ℕ, 0 < n ∧ (a : ℤ) - b = h.eval (n : ℤ)) →
      (A.card : ℝ) ≤ C * (N : ℝ) * Real.exp (-c * Real.sqrt (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ))))) →
    ∃ c > 0, ∃ C > 0, ∀ N : ℕ, 3 ≤ N →
      ∀ A ⊆ Finset.Icc 1 N,
      (∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬ ∃ n : ℕ, 0 < n ∧ (a : ℤ) - b = h.eval (n : ℤ)) →
      (A.card : ℝ) ≤ C * (N : ℝ) * Real.exp (-c * Real.sqrt (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ)))) := by
  rintro ⟨c, hcpos, C, hCpos, N₀, hN₀⟩
  set N₁ : ℕ := max N₀ 3 with hN₁
  set C' : ℝ := max C (Real.exp (c * Real.sqrt (Real.log (N₁ : ℝ) * Real.log (Real.log (N₁ : ℝ))))) with hC'
  refine ⟨c, hcpos, C', ?_, ?_⟩
  · rw [hC']
    exact lt_max_iff.mpr (Or.inl hCpos)
  · intro N hN A hA hdiff
    by_cases hNN₁ : N₁ ≤ N
    · have hN₀N : N₀ ≤ N := le_trans (le_max_left N₀ 3) hNN₁
      have hmain := hN₀ N hN₀N A hA hdiff
      have hCle : C ≤ C' := by rw [hC']; exact le_max_left _ _
      have hNnonneg : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      calc
        (A.card : ℝ) ≤ C * (N : ℝ) * Real.exp (-c * Real.sqrt (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ)))) := hmain
        _ ≤ C' * (N : ℝ) * Real.exp (-c * Real.sqrt (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ)))) := by
          apply mul_le_mul_of_nonneg_right
          · apply mul_le_mul_of_nonneg_right hCle hNnonneg
          · exact Real.exp_nonneg _
    · have hNlt : N < N₁ := Nat.lt_of_not_ge hNN₁
      have hAcard : A.card ≤ N := by
        have hcard := Finset.card_le_card hA
        simpa using hcard
      have hAcardR : (A.card : ℝ) ≤ (N : ℝ) := by exact_mod_cast hAcard
      have hN3 : 3 ≤ N := hN
      have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) hN3)
      have hlogN_gt_one : (1 : ℝ) < Real.log (N : ℝ) := by
        have hNR : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN3
        have hlog3le : Real.log 3 ≤ Real.log (N : ℝ) := Real.log_le_log (by norm_num) hNR
        linarith [Real.log_three_gt_d9, hlog3le]
      have hlogNpos : 0 < Real.log (N : ℝ) := by linarith
      have hloglogN_nonneg : 0 ≤ Real.log (Real.log (N : ℝ)) := Real.log_nonneg hlogN_gt_one.le
      have hN₁3 : 3 ≤ N₁ := le_max_right N₀ 3
      have hlogN₁_gt_one : (1 : ℝ) < Real.log (N₁ : ℝ) := by
        have hN₁R : (3 : ℝ) ≤ (N₁ : ℝ) := by exact_mod_cast hN₁3
        have hlog3le : Real.log 3 ≤ Real.log (N₁ : ℝ) := Real.log_le_log (by norm_num) hN₁R
        linarith [Real.log_three_gt_d9, hlog3le]
      have hlogN₁pos : 0 < Real.log (N₁ : ℝ) := by linarith
      have hlog_le : Real.log (N : ℝ) ≤ Real.log (N₁ : ℝ) := by
        apply Real.log_le_log hNpos
        exact_mod_cast le_of_lt hNlt
      have hloglog_le : Real.log (Real.log (N : ℝ)) ≤ Real.log (Real.log (N₁ : ℝ)) := by
        apply Real.log_le_log hlogNpos
        exact hlog_le
      have hE : Real.exp (c * Real.sqrt (Real.log (N₁ : ℝ) * Real.log (Real.log (N₁ : ℝ)))) ≤ C' := by
        rw [hC']
        exact le_max_right _ _
      have hone : (1 : ℝ) ≤ C' * Real.exp (-c * Real.sqrt (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ)))) := by
        have hprod_le : Real.log (N : ℝ) * Real.log (Real.log (N : ℝ)) ≤
            Real.log (N₁ : ℝ) * Real.log (Real.log (N₁ : ℝ)) := by
          exact mul_le_mul hlog_le hloglog_le hloglogN_nonneg hlogN₁pos.le
        have hsqrt_le : Real.sqrt (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ))) ≤
            Real.sqrt (Real.log (N₁ : ℝ) * Real.log (Real.log (N₁ : ℝ))) :=
          Real.sqrt_le_sqrt hprod_le
        have hcS_le : c * Real.sqrt (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ))) ≤
            c * Real.sqrt (Real.log (N₁ : ℝ) * Real.log (Real.log (N₁ : ℝ))) :=
          mul_le_mul_of_nonneg_left hsqrt_le hcpos.le
        have hexp_le : Real.exp (c * Real.sqrt (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ)))) ≤
            Real.exp (c * Real.sqrt (Real.log (N₁ : ℝ) * Real.log (Real.log (N₁ : ℝ)))) := by
          exact (Real.exp_le_exp).mpr hcS_le
        have hS_le_C' : Real.exp (c * Real.sqrt (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ)))) ≤ C' :=
          le_trans hexp_le hE
        have h := mul_le_mul_of_nonneg_right hS_le_C'
          (Real.exp_nonneg (-c * Real.sqrt (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ)))))
        have hL : Real.exp (c * Real.sqrt (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ)))) *
            Real.exp (-(c * Real.sqrt (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ))))) = 1 := by
          rw [← Real.exp_add]
          have hzero : c * Real.sqrt (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ))) +
              (-(c * Real.sqrt (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ))))) = 0 := by ring
          rw [hzero, Real.exp_zero]
        simpa [hL] using h
      calc
        (A.card : ℝ) ≤ (N : ℝ) := hAcardR
        _ = (N : ℝ) * 1 := by ring
        _ ≤ (N : ℝ) * (C' * Real.exp (-c * Real.sqrt (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ))))) := by
          exact mul_le_mul_of_nonneg_left hone hNpos.le
        _ = C' * (N : ℝ) * Real.exp (-c * Real.sqrt (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ)))) := by ring
