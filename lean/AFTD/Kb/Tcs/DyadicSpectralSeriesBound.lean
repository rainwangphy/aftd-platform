import AFTD.Prelude
import AFTD.Kb.Tcs.FourierApproximationConstant
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.Weight

/-!
# dyadic_spectral_series_bound

Topic: circuits   Node: dd675f338a62

Provenance: helper lemma. arXiv:2611.06451 Theorem 3.1 proof (eq. 18)

Let a ≥ 0, and let mu : ℕ+ → ℝ be a non-negative sequence satisfying ∑' j, mu j ≤ 1 and tail bounds ∑_{k > j} mu k ≤ (1/2)^j for all j ≥ 1. Then the series ∑' j, 2 * mu j * (j + 3)^a is bounded by 4 * K_a, where K_a = fourier_approximation_constant a.
-/

/-- The weight series defining the Fourier approximation constant is summable. -/
private lemma dyadic_spectral_series_bound_k_summable (a : ℝ) :
    Summable (fun j : ℕ+ => (1 / 2 : ℝ) ^ (j : ℕ) * ((j : ℝ) + 3) ^ a) := by
  obtain ⟨k, hk⟩ := exists_nat_ge a
  have hs0 : Summable (fun n : ℕ => (n : ℝ) ^ k * (1 / 2 : ℝ) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one k (by norm_num)
  have hs1 : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ)) ^ k * (1 / 2 : ℝ) ^ (n + 1)) := by
    have h := (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ k * (1 / 2 : ℝ) ^ n) 1).mpr hs0
    simpa [Nat.cast_add, Nat.cast_one] using h
  have hs2 : Summable (fun n : ℕ => (5 : ℝ) ^ k * ((((n + 1 : ℕ) : ℝ)) ^ k * (1 / 2 : ℝ) ^ (n + 1))) :=
    hs1.mul_left ((5 : ℝ) ^ k)
  rw [← Equiv.summable_iff (Equiv.pnatEquivNat.symm)]
  refine Summable.of_nonneg_of_le ?nonneg ?le hs2
  · intro n
    simp only [Function.comp_apply, Equiv.pnatEquivNat_symm_apply]
    apply mul_nonneg
    · positivity
    · exact Real.rpow_nonneg (by positivity) a
  · intro n
    simp only [Function.comp_apply, Equiv.pnatEquivNat_symm_apply]
    have hbase : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) + 3 := by
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) n]
    have hrpow : (((n + 1 : ℕ) : ℝ) + 3) ^ a ≤ (((n + 1 : ℕ) : ℝ) + 3) ^ k := by
      have h := Real.rpow_le_rpow_of_exponent_le hbase hk
      simpa [Real.rpow_natCast] using h
    have h4 : (((n + 1 : ℕ) : ℝ) + 3) ≤ 5 * (((n + 1 : ℕ) : ℝ)) := by
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hpow : (((n + 1 : ℕ) : ℝ) + 3) ^ k ≤ (5 * (((n + 1 : ℕ) : ℝ))) ^ k :=
      pow_le_pow_left₀ (by positivity) h4 k
    calc
      (1 / 2 : ℝ) ^ (n + 1) * (((n + 1 : ℕ) : ℝ) + 3) ^ a
          ≤ (1 / 2 : ℝ) ^ (n + 1) * (((n + 1 : ℕ) : ℝ) + 3) ^ k := by
            gcongr
      _ ≤ (1 / 2 : ℝ) ^ (n + 1) * (5 * (((n + 1 : ℕ) : ℝ))) ^ k := by gcongr
      _ = (5 : ℝ) ^ k * ((((n + 1 : ℕ) : ℝ)) ^ k * (1 / 2 : ℝ) ^ (n + 1)) := by
            rw [mul_pow]; ring

/-- Bound on the dyadic spectral series by the Fourier approximation constant. -/
theorem dyadic_spectral_series_bound (a : ℝ) (ha : 0 ≤ a) (mu : ℕ+ → ℝ)
    (hmu_nonneg : ∀ j, 0 ≤ mu j)
    (hmu_le_one : (∑' j, mu j) ≤ 1)
    (hmu_tail : ∀ j : ℕ+, (∑' k : ℕ+, if (j : ℕ) < (k : ℕ) then mu k else 0) ≤ (1 / 2 : ℝ) ^ (j : ℕ)) :
    (∑' j : ℕ+, 2 * mu j * ((j : ℝ) + 3) ^ a) ≤ 4 * fourier_approximation_constant a := by
  by_cases hmu_summable : Summable mu
  · have hmu_one_le_one : mu (1 : ℕ+) ≤ 1 := by
      have h := Summable.sum_le_tsum ({1} : Finset ℕ+) (fun i hi => hmu_nonneg i) hmu_summable
      simpa using h.trans hmu_le_one
    have hK_summable : Summable (fun j : ℕ+ => (1 / 2 : ℝ) ^ (j : ℕ) * ((j : ℝ) + 3) ^ a) :=
      dyadic_spectral_series_bound_k_summable a
    have hG_summable : Summable (fun j : ℕ+ => 4 * ((1 / 2 : ℝ) ^ (j : ℕ) * ((j : ℝ) + 3) ^ a)) :=
      hK_summable.mul_left 4
    have hFG : ∀ j : ℕ+, 2 * mu j * ((j : ℝ) + 3) ^ a
        ≤ 4 * ((1 / 2 : ℝ) ^ (j : ℕ) * ((j : ℝ) + 3) ^ a) := by
      intro j
      by_cases hj : j = 1
      · subst hj
        norm_num
        have h4 : (0 : ℝ) ≤ 4 ^ a := Real.rpow_nonneg (by norm_num) a
        nlinarith [hmu_one_le_one]
      · have hj2 : 2 ≤ (j : ℕ) := by
          have hcoe_ne : (j : ℕ) ≠ 1 := by
            intro h
            apply hj
            apply PNat.coe_inj.mp
            simpa using h
          have hp : 0 < (j : ℕ) := j.pos
          omega
        have hjp_lt : (((j - 1 : ℕ+) : ℕ)) < (j : ℕ) := by
          rw [PNat.sub_coe]
          have h1j : (1 : ℕ+) < j := by exact_mod_cast (by omega : 1 < (j : ℕ))
          simp [h1j]
        have htail_summable : Summable (fun k : ℕ+ => if (((j - 1 : ℕ+) : ℕ)) < (k : ℕ) then mu k else 0) := by
          refine Summable.of_nonneg_of_le ?_ ?_ hmu_summable
          · intro k
            split_ifs <;> simp [hmu_nonneg]
          · intro k
            split_ifs <;> simp [hmu_nonneg]
        have hterm : (if (((j - 1 : ℕ+) : ℕ)) < (j : ℕ) then mu j else 0)
            ≤ ∑' k : ℕ+, if (((j - 1 : ℕ+) : ℕ)) < (k : ℕ) then mu k else 0 := by
          refine Summable.le_tsum htail_summable j ?_
          intro k hk
          split_ifs <;> simp [hmu_nonneg]
        have hmuj_le : mu j ≤ (1 / 2 : ℝ) ^ (((j - 1 : ℕ+) : ℕ)) := by
          calc
            mu j = (if (((j - 1 : ℕ+) : ℕ)) < (j : ℕ) then mu j else 0) := by simp [hjp_lt]
            _ ≤ ∑' k : ℕ+, if (((j - 1 : ℕ+) : ℕ)) < (k : ℕ) then mu k else 0 := hterm
            _ ≤ (1 / 2 : ℝ) ^ (((j - 1 : ℕ+) : ℕ)) := hmu_tail (j - 1)
        have hpowrel : (1 / 2 : ℝ) ^ (((j - 1 : ℕ+) : ℕ)) = 2 * (1 / 2 : ℝ) ^ (j : ℕ) := by
          have hj_eq : (j : ℕ) = (((j - 1 : ℕ+) : ℕ)) + 1 := by
            rw [PNat.sub_coe]
            have h1j : (1 : ℕ+) < j := by exact_mod_cast (by omega : 1 < (j : ℕ))
            simp [h1j]
            omega
          rw [hj_eq, pow_succ]
          ring
        have hw : 0 ≤ ((j : ℝ) + 3) ^ a := Real.rpow_nonneg (by positivity) a
        calc
          2 * mu j * ((j : ℝ) + 3) ^ a
              ≤ 2 * (1 / 2 : ℝ) ^ (((j - 1 : ℕ+) : ℕ)) * ((j : ℝ) + 3) ^ a := by
                gcongr
          _ = 4 * ((1 / 2 : ℝ) ^ (j : ℕ) * ((j : ℝ) + 3) ^ a) := by
                rw [hpowrel]; ring
    have hF_summable : Summable (fun j : ℕ+ => 2 * mu j * ((j : ℝ) + 3) ^ a) := by
      refine Summable.of_nonneg_of_le ?_ hFG hG_summable
      intro j
      apply mul_nonneg
      · apply mul_nonneg; norm_num; exact hmu_nonneg j
      · exact Real.rpow_nonneg (by positivity) a
    have hle := Summable.tsum_le_tsum hFG hF_summable hG_summable
    calc
      (∑' j : ℕ+, 2 * mu j * ((j : ℝ) + 3) ^ a)
          ≤ ∑' j : ℕ+, 4 * ((1 / 2 : ℝ) ^ (j : ℕ) * ((j : ℝ) + 3) ^ a) := hle
      _ = 4 * fourier_approximation_constant a := by
            rw [tsum_mul_left]
            rfl
  · have hF_not_summable : ¬ Summable (fun j : ℕ+ => 2 * mu j * ((j : ℝ) + 3) ^ a) := by
      intro hF
      apply hmu_summable
      refine Summable.of_nonneg_of_le hmu_nonneg ?_ hF
      intro j
      have hbase : (1 : ℝ) ≤ (j : ℝ) + 3 := by
        have : (0 : ℝ) ≤ (j : ℝ) := by positivity
        linarith
      have hw1 : 1 ≤ ((j : ℝ) + 3) ^ a := Real.one_le_rpow hbase ha
      nlinarith [hmu_nonneg j, hw1]
    have hF_zero : (∑' j : ℕ+, 2 * mu j * ((j : ℝ) + 3) ^ a) = 0 :=
      tsum_eq_zero_of_not_summable hF_not_summable
    rw [hF_zero]
    have hK_nonneg : 0 ≤ fourier_approximation_constant a := by
      unfold fourier_approximation_constant
      refine tsum_nonneg (fun j => ?_)
      apply mul_nonneg
      · positivity
      · exact Real.rpow_nonneg (by positivity) a
    nlinarith
