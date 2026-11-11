import AFTD.Prelude
import AFTD.Kb.Tcs.NonzeroCubes

/-!
# subfield_nonzero_mem_cubes

Topic: cryptography   Node: 3474ef46ccbd

Provenance: helper lemma. arXiv:2611.10269 Sec. 7

Let E be a field, m an odd natural number, and t a nonzero element of E. If t^(2^m) = t, then t belongs to nonzero_cubes E.
-/

/-- For odd m, every nonzero element of the subfield F_{2^m} is a cube. -/
theorem subfield_nonzero_mem_cubes {E : Type*} [Field E] (m : ℕ) (hm : Odd m) (t : E) (ht : t ≠ 0) (htq : t ^ (2 ^ m) = t) : t ∈ nonzero_cubes E := by
  rcases hm with ⟨k, rfl⟩
  let N := 2 ^ (2 * k + 1) - 1
  have h2m : 2 ^ (2 * k + 1) = N + 1 := by
    dsimp [N]
    have hpos : 0 < 2 ^ (2 * k + 1) := Nat.pow_pos (by norm_num)
    omega
  have hpowN : t ^ N = 1 := by
    have h := htq
    rw [h2m, pow_succ] at h
    exact mul_right_cancel₀ ht (by simpa using h)
  have hdiv : 3 ∣ 2 * N + 1 := by
    dsimp [N]
    have hpow2 : 2 ^ (2 * k + 1) = 2 * 4 ^ k := by
      rw [pow_succ, pow_mul]
      norm_num
      exact Nat.mul_comm _ _
    have hd4 : 3 ∣ 4 * 4 ^ k - 1 := by
      have h4 : (4 : ℕ) ≡ 1 [MOD 3] := by norm_num [Nat.ModEq]
      have hpow : (4 : ℕ) ^ k ≡ 1 [MOD 3] := by simpa using h4.pow k
      have hmul : 4 * (4 : ℕ) ^ k ≡ 4 * 1 [MOD 3] := (Nat.ModEq.refl 4).mul hpow
      have hmul' : 4 * (4 : ℕ) ^ k ≡ 1 [MOD 3] := hmul.trans h4
      have h : 1 ≤ 4 * 4 ^ k := Nat.one_le_iff_ne_zero.mpr (by positivity)
      exact (Nat.modEq_iff_dvd' h).mp hmul'.symm
    convert hd4 using 1
    rw [hpow2]
    have ha : 1 ≤ 4 ^ k := by exact Nat.one_le_pow k 4 (by norm_num)
    omega
  let c := (2 * N + 1) / 3
  have hc : 3 * c = 2 * N + 1 := by
    dsimp [c]
    exact Nat.mul_div_cancel' hdiv
  have htrip : t ^ (3 * c) = t := by
    have h2N : t ^ (2 * N) = 1 := by
      calc
        t ^ (2 * N) = t ^ (N * 2) := by rw [Nat.mul_comm]
        _ = (t ^ N) ^ 2 := by rw [pow_mul]
        _ = 1 := by rw [hpowN]; norm_num
    rw [hc, pow_add, h2N, one_mul, pow_one]
  refine ⟨t ^ c, ?_, ?_⟩
  · exact pow_ne_zero c ht
  · calc
      (t ^ c) ^ 3 = t ^ (c * 3) := (pow_mul t c 3).symm
      _ = t ^ (3 * c) := by rw [Nat.mul_comm]
      _ = t := htrip
