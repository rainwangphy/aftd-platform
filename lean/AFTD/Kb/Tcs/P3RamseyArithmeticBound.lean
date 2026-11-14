import AFTD.Prelude

/-!
# p3_ramsey_arithmetic_bound

Topic: combinatorics   Node: 1c62adb37490

Provenance: helper lemma. arXiv:2611.15376 Lemma 2.1

For all integers a ≥ b ≥ 1 and any natural number N, b * (N choose 2) ≤ a * ⌊N / 2⌋ holds if and only if N ≤ 2 * ⌊(a + b) / (2 * b)⌋.
-/

/-- Equivalence between the matching edge count bound b * choose(N, 2) ≤ a * ⌊N/2⌋ and N ≤ 2 * ⌊(a+b)/(2b)⌋. -/
theorem p3_ramsey_arithmetic_bound (a b N : ℕ) (hba : b ≤ a) (hb : 1 ≤ b) :
    b * N.choose 2 ≤ a * (N / 2) ↔ N ≤ 2 * ((a + b) / (2 * b)) := by
  have hden : 0 < 2 * b := by omega
  rcases Nat.even_or_odd N with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hN : N = 2*k := by omega
    rw [hN]
    have hchoose : (2*k).choose 2 = k * (2*k - 1) := by
      rw [Nat.choose_two_right]
      have h : (2*k) * (2*k - 1) = 2 * (k * (2*k - 1)) := by ring
      rw [h, Nat.mul_div_right _ (by norm_num : 0 < 2)]
    have hdiv2 : (2*k) / 2 = k := by omega
    rw [hchoose, hdiv2]
    by_cases hk0 : k = 0
    · subst k
      simp
    · have hkpos : 0 < k := by omega
      have hL : b * (k * (2*k - 1)) ≤ a * k ↔ b * (2*k - 1) ≤ a := by
        have h1 : b * (k * (2*k - 1)) = k * (b*(2*k-1)) := by ring
        have h2 : a * k = k * a := by ring
        rw [h1, h2]
        exact Nat.mul_le_mul_left_iff hkpos
      have hA : b * (2*k - 1) ≤ a ↔ 2*b*k ≤ a + b := by
        constructor
        · intro h
          have h' : b*(2*k-1) + b ≤ a + b := Nat.add_le_add_right h b
          have hEq : b*(2*k-1) + b = 2*b*k := by
            have hsub : 1 ≤ 2*k := by omega
            calc
              b*(2*k-1) + b = b*((2*k-1)+1) := by ring
              _ = b*(2*k) := by rw [Nat.sub_add_cancel hsub]
              _ = 2*b*k := by ring
          omega
        · intro h
          have hsub : 1 ≤ 2*k := by omega
          have hEq : b*(2*k-1) + b = 2*b*k := by
            calc
              b*(2*k-1) + b = b*((2*k-1)+1) := by ring
              _ = b*(2*k) := by rw [Nat.sub_add_cancel hsub]
              _ = 2*b*k := by ring
          omega
      rw [hL, hA]
      have hR : (2*k ≤ 2*((a+b)/(2*b))) ↔ k*(2*b) ≤ a+b := by
        rw [show (2*k ≤ 2*((a+b)/(2*b))) ↔ k ≤ (a+b)/(2*b) by omega]
        rw [Nat.le_div_iff_mul_le hden]
      rw [hR]
      constructor <;> intro h
      · have : k*(2*b) = 2*b*k := by ring
        omega
      · have : k*(2*b) = 2*b*k := by ring
        omega
  · have hN : N = 2*k+1 := by omega
    rw [hN]
    have hchoose : (2*k+1).choose 2 = k * (2*k+1) := by
      rw [Nat.choose_two_right]
      have hsub : 2*k+1 - 1 = 2*k := by omega
      rw [hsub]
      have h : (2*k+1) * (2*k) = 2 * (k * (2*k+1)) := by ring
      rw [h, Nat.mul_div_right _ (by norm_num : 0 < 2)]
    have hdiv2 : (2*k+1) / 2 = k := by omega
    rw [hchoose, hdiv2]
    by_cases hk0 : k = 0
    · subst k
      have hq : 1 ≤ (a+b)/(2*b) := by
        rw [Nat.le_div_iff_mul_le hden]
        omega
      norm_num
      omega
    · have hkpos : 0 < k := by omega
      have hL : b * (k * (2*k+1)) ≤ a * k ↔ b * (2*k+1) ≤ a := by
        have h1 : b * (k * (2*k+1)) = k * (b*(2*k+1)) := by ring
        have h2 : a * k = k * a := by ring
        rw [h1, h2]
        exact Nat.mul_le_mul_left_iff hkpos
      have hA : b * (2*k+1) ≤ a ↔ 2*b*(k+1) ≤ a+b := by
        constructor
        · intro h
          have h' : b*(2*k+1) + b ≤ a + b := Nat.add_le_add_right h b
          have hEq : b*(2*k+1) + b = 2*b*(k+1) := by ring
          omega
        · intro h
          have hEq : b*(2*k+1) + b = 2*b*(k+1) := by ring
          omega
      rw [hL, hA]
      have hR : (2*k+1 ≤ 2*((a+b)/(2*b))) ↔ (k+1)*(2*b) ≤ a+b := by
        rw [show (2*k+1 ≤ 2*((a+b)/(2*b))) ↔ k+1 ≤ (a+b)/(2*b) by omega]
        rw [Nat.le_div_iff_mul_le hden]
      rw [hR]
      constructor <;> intro h
      · have : 2*b*(k+1) = (k+1)*(2*b) := by ring
        omega
      · have : 2*b*(k+1) = (k+1)*(2*b) := by ring
        omega
