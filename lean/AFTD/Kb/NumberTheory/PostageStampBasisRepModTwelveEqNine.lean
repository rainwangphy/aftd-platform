import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# postage_stamp_basis_rep_mod_twelve_eq_nine

Topic: elementary_number_theory   Node: 5cdc9301978d

Provenance: helper lemma. step towards postage_stamp_basis_range_neg_ge_of_mod_twelve_eq_nine

For any r : ℕ and any m ≤ 36r² + 72r + 33, there exist non-negative integers s, t, u such that s + t + u = 12r + 9 and -s(2r+2) + t(2r+2) + u(4r+5) = m.
-/

lemma postage_stamp_basis_rep_mod_twelve_eq_nine_core_int
    (R u0 q : ℤ) (hR : 1 ≤ R) (hu0 : 0 ≤ u0) (huw : u0 < 2*R)
    (hq0 : 0 ≤ q)
    (hbound : 2*R*q + u0 ≤ 36*R^2 - 3) :
    ∃ j s t : ℤ, 0 ≤ j ∧ j ≤ 4 ∧ 0 ≤ s ∧ 0 ≤ t ∧
      2*s = 12*R - 3 + u0 - q + j*(2*R+1) ∧
      2*t = 12*R - 3 - 3*u0 + q - j*(6*R+1) ∧
      s + t + u0 + j*(2*R) = 12*R - 3 := by
  rcases Int.even_or_odd' (1 + q + u0) with ⟨d, hd | hd⟩
  · have hqdef : q = 2*d - 1 - u0 := by linarith
    have hqle : q ≤ 18*R - 1 := by nlinarith
    by_cases h4 : 4*(6*R+1) ≤ 12*R + q - 3*u0 - 3
    · refine ⟨4, 10*R + 1 + u0 - d, d - 6*R - 4 - 2*u0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · norm_num
      · norm_num
      · have hj4 : 6*R + 2*u0 + 4 ≤ d := by nlinarith
        nlinarith
      · have hj4 : 6*R + 2*u0 + 4 ≤ d := by nlinarith
        nlinarith
      · nlinarith
      · nlinarith
      · nlinarith
    · by_cases h2 : 2*(6*R+1) ≤ 12*R + q - 3*u0 - 3
      · refine ⟨2, 8*R + u0 - d, d - 2*u0 - 3, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · norm_num
        · norm_num
        · have hj4 : d < 6*R + 2*u0 + 4 := by nlinarith
          by_cases hlow : u0 ≤ 2*R - 3
          · nlinarith
          · have hhigh : u0 = 2*R - 2 ∨ u0 = 2*R - 1 := by omega
            rcases hhigh with h | h <;> subst u0 <;> nlinarith
        · have hj2 : 2*u0 + 3 ≤ d := by nlinarith
          nlinarith
        · nlinarith
        · nlinarith
        · nlinarith
      · refine ⟨0, 6*R - 1 + u0 - d, 6*R - 2 - 2*u0 + d, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · norm_num
        · norm_num
        · have hj2 : d < 2*u0 + 3 := by nlinarith
          nlinarith
        · have hj2 : d < 2*u0 + 3 := by nlinarith
          nlinarith
        · nlinarith
        · nlinarith
        · nlinarith
  · have hqdef : q = 2*d - u0 := by linarith
    have hqle : q ≤ 18*R - 1 := by nlinarith
    by_cases h3 : 3*(6*R+1) ≤ 12*R + q - 3*u0 - 3
    · refine ⟨3, 9*R + u0 - d, d - 3*R - 2*u0 - 3, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · norm_num
      · norm_num
      · nlinarith
      · have hj3 : 3*R + 2*u0 + 3 ≤ d := by nlinarith
        nlinarith
      · nlinarith
      · nlinarith
      · nlinarith
    · refine ⟨1, 7*R - 1 + u0 - d, 3*R - 2 - 2*u0 + d, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · norm_num
      · norm_num
      · have hj3 : d < 3*R + 2*u0 + 3 := by nlinarith
        nlinarith
      · nlinarith
      · nlinarith
      · nlinarith
      · nlinarith

/-- Every non-negative integer m ≤ 36r² + 72r + 33 can be represented as -s(2r+2) + t(2r+2) + u(4r+5) for non-negative integers s, t, u with s + t + u = 12r + 9. -/
theorem postage_stamp_basis_rep_mod_twelve_eq_nine (r : ℕ) (m : ℕ)
    (hm : m ≤ 36 * r ^ 2 + 72 * r + 33) :
    ∃ s t u : ℕ, s + t + u = 12 * r + 9 ∧
      - (s : ℤ) * (2 * r + 2) + (t : ℤ) * (2 * r + 2) + (u : ℤ) * (4 * r + 5) = (m : ℤ) := by
  let R : ℕ := r + 1
  have hR : 1 ≤ R := by omega
  have hmR : m ≤ 36 * R^2 - 3 := by
    dsimp [R]
    have hsq : 36 * (r+1)^2 = 36 * r ^ 2 + 72 * r + 36 := by ring
    omega
  let w : ℕ := 2 * R
  have hwpos : 0 < w := by omega
  let q : ℕ := m / w
  let u0 : ℕ := m % w
  have hm_eq : m = q * w + u0 := by
    dsimp [q, u0, w]
    have h := Nat.div_add_mod m (2*R)
    rw [mul_comm] at h
    exact h.symm
  have hu0w : u0 < w := by
    dsimp [u0, w]
    exact Nat.mod_lt m (by positivity)
  have hm_eq' : m = q * (2*R) + u0 := by simpa [w] using hm_eq
  have hbound_nat : q * (2*R) + u0 ≤ 36 * R^2 - 3 := by
    rw [← hm_eq']
    exact hmR
  have h3 : 3 ≤ 36*R^2 := by nlinarith [hR]
  have hmZ : (m:ℤ) = (q:ℤ)*(2*(R:ℤ)) + (u0:ℤ) := by
    exact_mod_cast hm_eq'
  have hmRZ : (m:ℤ) ≤ 36*(R:ℤ)^2 - 3 := by
    have hcast : ((36*R^2 - 3 : ℕ) : ℤ) = 36*(R:ℤ)^2 - 3 := by
      rw [Nat.cast_sub h3]
      norm_num
    rw [← hcast]
    exact_mod_cast hmR
  have hbound_int : 2*(R:ℤ)*(q:ℤ) + (u0:ℤ) ≤ 36*(R:ℤ)^2 - 3 := by
    nlinarith
  have hRint : (1:ℤ) ≤ (R:ℤ) := by exact_mod_cast hR
  have hu0int : (0:ℤ) ≤ (u0:ℤ) := by positivity
  have huww_int : (u0:ℤ) < 2*(R:ℤ) := by exact_mod_cast hu0w
  have hqint : (0:ℤ) ≤ (q:ℤ) := by positivity
  obtain ⟨j, sI, tI, hj0, hj4, hs0, ht0, hSeq, hTeq, hSum⟩ :=
    postage_stamp_basis_rep_mod_twelve_eq_nine_core_int (R:ℤ) (u0:ℤ) (q:ℤ) hRint hu0int huww_int hqint hbound_int
  let jn : ℕ := j.toNat
  let s : ℕ := sI.toNat
  let t : ℕ := tI.toNat
  have hjcast : (jn:ℤ) = j := Int.toNat_of_nonneg hj0
  have hscast : (s:ℤ) = sI := Int.toNat_of_nonneg hs0
  have htcast : (t:ℤ) = tI := Int.toNat_of_nonneg ht0
  let u : ℕ := u0 + jn * (2*R)
  have hucast : (u:ℤ) = (u0:ℤ) + (jn:ℤ)*(2*R) := by
    dsimp [u]
  have hsum_int : (s:ℤ) + (t:ℤ) + (u:ℤ) = 12*(R:ℤ) - 3 := by
    rw [hscast, htcast, hucast, hjcast]
    linarith
  have hsum_nat : s + t + u = 12 * R - 3 := by
    have hR3 : 3 ≤ 12 * R := by omega
    omega
  refine ⟨s, t, u, ?_, ?_⟩
  · have hh : 12 * R - 3 = 12 * r + 9 := by dsimp [R]; omega
    rw [← hh]
    exact hsum_nat
  · have hc1 : (2 * (r:ℤ) + 2) = 2 * (R:ℤ) := by dsimp [R]; ring
    have hc2 : (4 * (r:ℤ) + 5) = 4 * (R:ℤ) + 1 := by dsimp [R]; ring
    rw [hc1, hc2]
    have hval_aux : - sI*(2*(R:ℤ)) + tI*(2*(R:ℤ)) + ((u0:ℤ)+j*(2*(R:ℤ)))*(4*(R:ℤ)+1) = (q:ℤ)*(2*(R:ℤ))+(u0:ℤ) := by
      linear_combination (-(R:ℤ)) * hSeq + (R:ℤ) * hTeq
    rw [hscast, htcast, hucast, hjcast]
    rw [hmZ]
    exact hval_aux
