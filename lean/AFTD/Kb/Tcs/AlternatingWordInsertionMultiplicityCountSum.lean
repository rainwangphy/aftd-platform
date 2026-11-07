import AFTD.Prelude

/-!
# alternating_word_insertion_multiplicity_count_sum

Topic: information   Node: 50a8d78d2e1c

Provenance: formalization of a published result. Source: arXiv:2611.01064 Section 5.1

For all natural numbers m and k, the sum over t from 0 to k / 2 of Nat.choose (m + 1) (k - 2 * t) * Nat.choose (m + t) t equals Nat.choose (m + k) k.
-/

open PowerSeries in
private lemma zz_coeff_one_add_X_pow_ps (n i : ℕ) :
    PowerSeries.coeff i ((1 + PowerSeries.X : PowerSeries ℤ) ^ n) = ((n.choose i : ℕ) : ℤ) := by
  have h2 : ((1 + Polynomial.X : Polynomial ℤ) : PowerSeries ℤ) = (1 + PowerSeries.X : PowerSeries ℤ) := by
    simp
  rw [← h2, ← Polynomial.coe_pow, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]

private lemma zz_coeff_subst_sq_ps (m n : ℕ) :
    PowerSeries.coeff n (PowerSeries.subst (PowerSeries.X ^ 2 : PowerSeries ℤ)
      (PowerSeries.mk fun k => ((m + k).choose m : ℤ)))
      = if 2 ∣ n then ((m + n / 2).choose m : ℤ) else 0 := by
  rw [PowerSeries.coeff_subst_X_pow (by norm_num : (2 : ℕ) ≠ 0)]
  simp [PowerSeries.coeff_mk]

private lemma zz_ps_gf (m : ℕ) :
    (1 + PowerSeries.X : PowerSeries ℤ) ^ (m + 1) *
      PowerSeries.subst (PowerSeries.X ^ 2 : PowerSeries ℤ)
        (PowerSeries.mk fun n => ((m + n).choose m : ℤ)) =
    PowerSeries.mk fun n => ((m + n).choose m : ℤ) := by
  have hh : PowerSeries.HasSubst (PowerSeries.X ^ 2 : PowerSeries ℤ) :=
    PowerSeries.HasSubst.X_pow (by norm_num : (2 : ℕ) ≠ 0)
  set Ψ : PowerSeries ℤ := PowerSeries.mk fun n => ((m + n).choose m : ℤ) with hΨ
  set S : PowerSeries ℤ := PowerSeries.subst (PowerSeries.X ^ 2) Ψ with hS
  have hΨD : Ψ * (1 - PowerSeries.X : PowerSeries ℤ) ^ (m + 1) = 1 :=
    PowerSeries.mk_add_choose_mul_one_sub_pow_eq_one ℤ m
  have hsub : PowerSeries.subst (PowerSeries.X ^ 2 : PowerSeries ℤ)
        ((1 - PowerSeries.X : PowerSeries ℤ) ^ (m + 1))
      = (1 - PowerSeries.X ^ 2 : PowerSeries ℤ) ^ (m + 1) := by
    rw [PowerSeries.subst_pow hh, PowerSeries.subst_sub hh, PowerSeries.subst_X hh,
      ← PowerSeries.coe_substAlgHom hh, map_one]
  have hSD : S * (1 - PowerSeries.X ^ 2 : PowerSeries ℤ) ^ (m + 1) = 1 := by
    rw [hS, ← hsub, ← PowerSeries.subst_mul hh, hΨD, ← PowerSeries.coe_substAlgHom hh, map_one]
  have hΦD : (1 + PowerSeries.X : PowerSeries ℤ) ^ (m + 1) *
      (1 - PowerSeries.X : PowerSeries ℤ) ^ (m + 1) =
      (1 - PowerSeries.X ^ 2 : PowerSeries ℤ) ^ (m + 1) := by
    rw [← mul_pow]; ring
  have h1 : (1 + PowerSeries.X : PowerSeries ℤ) ^ (m + 1) * S *
      (1 - PowerSeries.X : PowerSeries ℤ) ^ (m + 1) = 1 := by
    have hrw : (1 + PowerSeries.X : PowerSeries ℤ) ^ (m + 1) * S *
        (1 - PowerSeries.X : PowerSeries ℤ) ^ (m + 1)
        = S * ((1 + PowerSeries.X : PowerSeries ℤ) ^ (m + 1) *
          (1 - PowerSeries.X : PowerSeries ℤ) ^ (m + 1)) := by ring
    rw [hrw, hΦD, hSD]
  have hne : (1 - PowerSeries.X : PowerSeries ℤ) ^ (m + 1) ≠ 0 := by
    have h1X : (1 - PowerSeries.X : PowerSeries ℤ) ≠ 0 := by
      intro h
      have hc := congrArg PowerSeries.constantCoeff h
      simp at hc
    exact pow_ne_zero _ h1X
  refine mul_right_cancel₀ hne ?_
  rw [h1, hΨD]

private lemma zz_reindex (m k : ℕ) :
    (∑ i ∈ (Finset.range (k + 1)).filter (fun i => 2 ∣ (k - i)),
        ((m + 1).choose i : ℤ) * ((m + (k - i) / 2).choose m : ℤ))
      = ∑ t ∈ Finset.range (k / 2 + 1), ((m + 1).choose (k - 2 * t) : ℤ) *
          ((m + t).choose t : ℤ) := by
  have hdvd : ∀ i, i ∈ (Finset.range (k + 1)).filter (fun i => 2 ∣ (k - i)) →
      k - 2 * ((k - i) / 2) = i := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨hik, c, hc⟩ := hi
    omega
  refine Finset.sum_bij (fun i _ => (k - i) / 2) ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    simp only [Finset.mem_range]; omega
  · intro i1 h1 i2 h2 he
    have e1 := hdvd i1 h1
    have e2 := hdvd i2 h2
    rw [← e1, ← e2, he]
  · intro t ht
    simp only [Finset.mem_range] at ht
    refine ⟨k - 2 * t, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, ⟨t, by omega⟩⟩
    · show (k - (k - 2 * t)) / 2 = t
      rw [show k - (k - 2 * t) = 2 * t by omega, Nat.mul_div_cancel_left t (by norm_num)]
  · intro i hi
    have e := hdvd i hi
    show ((m + 1).choose i : ℤ) * ((m + (k - i) / 2).choose m : ℤ)
      = ((m + 1).choose (k - 2 * ((k - i) / 2)) : ℤ) *
        ((m + (k - i) / 2).choose ((k - i) / 2) : ℤ)
    rw [e, Nat.choose_symm_add]

private lemma zz_main_sum (m k : ℕ) :
    ∑ t ∈ Finset.range (k / 2 + 1), (((m + 1).choose (k - 2 * t) : ℕ) : ℤ) *
      (((m + t).choose t : ℕ) : ℤ) = (((m + k).choose k : ℕ) : ℤ) := by
  have hcoeff := congrArg (PowerSeries.coeff k) (zz_ps_gf m)
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hcoeff
  simp only [zz_coeff_one_add_X_pow_ps, zz_coeff_subst_sq_ps, PowerSeries.coeff_mk] at hcoeff
  have hA : (∑ x ∈ Finset.range (k + 1),
      (if 2 ∣ (k - x) then ((m + 1).choose x : ℤ) * ((m + (k - x) / 2).choose m : ℤ) else 0))
      = ((m + k).choose m : ℤ) := by
    rw [← hcoeff]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    split_ifs <;> simp
  have hB : (∑ x ∈ (Finset.range (k + 1)).filter (fun i => 2 ∣ (k - i)),
      ((m + 1).choose x : ℤ) * ((m + (k - x) / 2).choose m : ℤ))
      = ((m + k).choose m : ℤ) := by
    rw [Finset.sum_filter]
    exact hA
  have hsym : ((m + k).choose k : ℤ) = ((m + k).choose m : ℤ) := by
    rw [Nat.choose_symm_add]
  rw [hsym, ← zz_reindex m k]
  exact hB

/-- Consistency identity summing multiplicity times count for the alternating word insertion histogram. -/
theorem alternating_word_insertion_multiplicity_count_sum (m k : ℕ) :
    ∑ t ∈ Finset.range (k / 2 + 1), (m + 1).choose (k - 2 * t) * (m + t).choose t = (m + k).choose k := by
  have h2 : ((∑ t ∈ Finset.range (k / 2 + 1),
      (m + 1).choose (k - 2 * t) * (m + t).choose t : ℕ) : ℤ) = (((m + k).choose k : ℕ) : ℤ) := by
    push_cast
    exact zz_main_sum m k
  exact Nat.cast_injective h2
