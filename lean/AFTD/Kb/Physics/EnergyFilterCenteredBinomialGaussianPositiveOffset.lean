import AFTD.Prelude

/-!
# energy_filter_centered_binomial_gaussian_positive_offset

Topic: statistical_mechanics   Node: ba09a9c57785

Provenance: helper lemma. OP-892: zero-extended centered binomial estimates.

For k≥1 and 0≤j≤k, the ratio choose(2k,k+j)/choose(2k,k) is at most exp(−j²/(2k)).
-/

theorem energy_filter_centered_binomial_gaussian_positive_offset
    (k j : ℕ) (hk : 1 ≤ k) (hj : j ≤ k) :
    (Nat.choose (2*k) (k+j) : ℝ) / (Nat.choose (2*k) k : ℝ) ≤
      Real.exp (-((j:ℝ)^2 / (2*(k:ℝ)))) := by
  revert hj
  induction j with
  | zero =>
    intro hj
    have hc : (Nat.choose (2*k) k : ℝ) ≠ 0 := by exact_mod_cast Nat.centralBinom_ne_zero k
    simp [hc]
  | succ j ih =>
    intro hj
    have hjk : j ≤ k := by omega
    have hjlt : j < k := by omega
    have hkpos : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hjreal : (j:ℝ) ≤ k := by exact_mod_cast hjk
    have hjone : (j:ℝ) + 1 ≤ k := by exact_mod_cast hj
    have hc : (Nat.choose (2*k) k : ℝ) ≠ 0 := by exact_mod_cast Nat.centralBinom_ne_zero k
    have hd : 0 < (k:ℝ)+j+1 := by positivity
    have he := Nat.choose_succ_right_eq (2*k) (k+j)
    have hsub : 2*k-(k+j)=k-j := by omega
    rw [hsub] at he
    have her : (Nat.choose (2*k) (k+j+1) : ℝ) * (((k+j+1:ℕ):ℝ)) =
        (Nat.choose (2*k) (k+j) : ℝ) * (((k-j:ℕ):ℝ)) := by exact_mod_cast he
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_one, Nat.cast_sub hjk] at her
    have hrec : (Nat.choose (2*k) (k+(j+1)) : ℝ) / (Nat.choose (2*k) k : ℝ) =
        ((Nat.choose (2*k) (k+j) : ℝ) / (Nat.choose (2*k) k : ℝ)) *
          (((k:ℝ)-j) / ((k:ℝ)+j+1)) := by
      rw [show k+(j+1)=k+j+1 by omega]
      field_simp
      nlinarith [her]
    have hstep : ((k:ℝ)-j) / ((k:ℝ)+j+1) ≤
        Real.exp (-((2*(j:ℝ)+1)/(2*(k:ℝ)))) := by
      have hden : (k:ℝ)+j+1 ≤ 2*(k:ℝ) := by linarith
      have hnum : 0 ≤ 2*(j:ℝ)+1 := by positivity
      have hfrac : (2*(j:ℝ)+1)/(2*(k:ℝ)) ≤
          (2*(j:ℝ)+1)/((k:ℝ)+j+1) := by
        exact div_le_div_of_nonneg_left hnum hd hden
      have hiden : ((k:ℝ)-j)/((k:ℝ)+j+1) =
          1 - (2*(j:ℝ)+1)/((k:ℝ)+j+1) := by field_simp; ring
      have hexp := Real.add_one_le_exp (-((2*(j:ℝ)+1)/(2*(k:ℝ))))
      rw [hiden]
      linarith
    have hfactor : 0 ≤ ((k:ℝ)-j)/((k:ℝ)+j+1) := div_nonneg (sub_nonneg.mpr hjreal) (le_of_lt hd)
    rw [Nat.cast_add, Nat.cast_one]
    rw [hrec]
    calc
      _ ≤ Real.exp (-((j:ℝ)^2 / (2*(k:ℝ)))) *
          Real.exp (-((2*(j:ℝ)+1)/(2*(k:ℝ)))) :=
        mul_le_mul (ih hjk) hstep hfactor (Real.exp_nonneg _)
      _ = _ := by
        rw [← Real.exp_add]
        congr 1
        ring
