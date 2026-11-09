import AFTD.Prelude
import AFTD.Kb.Tcs.IsBent
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# symmetric_counterexample_bent_weight_diff_div_sixteen

Topic: combinatorics   Node: 92c510018de2

Provenance: formalization of a published result. Source: arXiv:2611.06744, Section 3.4

For any even n ≥ 8 and any two bent functions g and h on (Fin n → ZMod 2), the difference between the Hamming weight of h and the Hamming weight of g is divisible by 16 in the integers.
-/

/-- The difference between the Hamming weights of two bent functions in n variables is divisible by 16 for n ≥ 8. -/
theorem symmetric_counterexample_bent_weight_diff_div_sixteen (n : ℕ) (hn_even : Even n) (hn8 : 8 ≤ n) (g h : (Fin n → ZMod 2) → ZMod 2) (hg : is_bent g) (hh : is_bent h) : (16 : ℤ) ∣ (((Finset.filter (fun x => h x = 1) Finset.univ).card : ℤ) - ((Finset.filter (fun x => g x = 1) Finset.univ).card : ℤ)) := by
  have _ := hn_even
  have h_sum (f : (Fin n → ZMod 2) → ZMod 2) :
    (∑ x : Fin n → ZMod 2, if f x = 0 then (1 : ℤ) else -1) =
      ((Finset.univ : Finset (Fin n → ZMod 2)).card : ℤ) - 2 * ((Finset.filter (fun x => f x = 1) Finset.univ).card : ℤ) := by
    have h_term : ∀ x : Fin n → ZMod 2,
      (if f x = 0 then (1 : ℤ) else -1) = 1 - 2 * (if f x = 1 then (1 : ℤ) else 0) := by
      intro x
      generalize f x = a
      fin_cases a <;> decide
    simp_rw [h_term]
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_one, ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_boole]

  have hg0 := hg 0
  have hh0 := hh 0
  have h_zero : ∀ x : Fin n → ZMod 2, (∑ i : Fin n, x i * (0 : Fin n → ZMod 2) i) = 0 := by
    intro x
    simp
  simp_rw [h_zero, add_zero] at hg0 hh0

  have hg_cases := eq_or_eq_neg_of_abs_eq hg0
  have hh_cases := eq_or_eq_neg_of_abs_eq hh0
  rw [h_sum g] at hg_cases
  rw [h_sum h] at hh_cases

  have h4 : 4 ≤ n / 2 := by omega
  have h16 : (16 : ℤ) ∣ (2 : ℤ) ^ (n / 2) := by
    have : (16 : ℤ) = (2 : ℤ) ^ 4 := by norm_num
    rw [this]
    exact pow_dvd_pow (2 : ℤ) h4

  set Wg := ((Finset.filter (fun x => g x = 1) Finset.univ).card : ℤ)
  set Wh := ((Finset.filter (fun x => h x = 1) Finset.univ).card : ℤ)
  set U := ((Finset.univ : Finset (Fin n → ZMod 2)).card : ℤ)
  set P := (2 : ℤ) ^ (n / 2)

  rcases hg_cases with hg_val | hg_val <;> rcases hh_cases with hh_val | hh_val
  · have : Wh - Wg = 0 := by linarith
    rw [this]
    exact dvd_zero 16
  · have : Wh - Wg = P := by linarith
    rw [this]
    exact h16
  · have : Wh - Wg = -P := by linarith
    rw [this]
    exact dvd_neg.mpr h16
  · have : Wh - Wg = 0 := by linarith
    rw [this]
    exact dvd_zero 16
