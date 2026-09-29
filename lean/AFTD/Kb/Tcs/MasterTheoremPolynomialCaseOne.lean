import AFTD.Prelude
import AFTD.Kb.Tcs.DivideAndConquerUnequalRootsRecurrence
import AFTD.Kb.Tcs.DivideAndConquerRecursionTree

/-!
# master_theorem_polynomial_case_one

Topic: algorithms   Node: e16623ddf186

Let a ≥ 0, b > 1 and c ≥ 0 be real numbers, d a natural number, and T : ℕ → ℝ a sequence with T(0) ≥ 0 satisfying the master recurrence at problem size n = b^k, namely T(k+1) = a·T(k) + c·b^{d(k+1)}. If a < b^d (the driving term c·n^d dominates), then for every k ≥ 1 the value T(k) is Θ(n^d) with n = b^k, in the explicit two-sided form c·(b^d)^k ≤ T(k) ≤ (T(0) + c·b^d/(b^d − a))·(b^d)^k.
-/

theorem master_theorem_polynomial_case_one (T : ℕ → ℝ) (a b c : ℝ) (d : ℕ)
    (hrec : ∀ k : ℕ, T (k + 1) = a * T k + c * b ^ (d * (k + 1)))
    (hT0 : 0 ≤ T 0) (ha : 0 ≤ a) (hb : 1 < b) (hc : 0 ≤ c) (hlt : a < b ^ d) :
    ∀ k : ℕ, 1 ≤ k →
      c * (b ^ d) ^ k ≤ T k ∧ T k ≤ (T 0 + c * b ^ d / (b ^ d - a)) * (b ^ d) ^ k := by
  intro k hk
  set R : ℝ := b ^ d with hR
  have hb0 : 0 < b := by linarith
  have hRpos : 0 < R := by rw [hR]; positivity
  have hRnn : 0 ≤ R := le_of_lt hRpos
  have hltR : a < R := by rw [hR]; exact hlt
  have hne : a ≠ R := ne_of_lt hltR
  have hden : 0 < R - a := by linarith
  have hrecR : ∀ k : ℕ, T (k + 1) = a * T k + c * R ^ (k + 1) := by
    intro k
    rw [hrec k, hR, pow_mul]
  have hformula :=
    divide_and_conquer_unequal_roots_recurrence T a R c (T 0) hne rfl hrecR
  have hRk : a ^ k ≤ R ^ k := pow_le_pow_left₀ ha (le_of_lt hltR) k
  have heq : (a ^ k - R ^ k) / (a - R) = (R ^ k - a ^ k) / (R - a) := by
    have h1 : a - R ≠ 0 := by linarith
    have h2 : R - a ≠ 0 := by linarith
    field_simp
    ring
  have hupper : T k ≤ (T 0 + c * R / (R - a)) * R ^ k := by
    rw [hformula k, heq]
    have h1 : T 0 * a ^ k ≤ T 0 * R ^ k := mul_le_mul_of_nonneg_left hRk hT0
    have hfac : 0 ≤ c * R / (R - a) := div_nonneg (mul_nonneg hc hRnn) (le_of_lt hden)
    have hdiff : R ^ k - a ^ k ≤ R ^ k := by
      have : 0 ≤ a ^ k := pow_nonneg ha k
      linarith
    have h2 : c * R * ((R ^ k - a ^ k) / (R - a)) ≤ c * R * R ^ k / (R - a) := by
      calc c * R * ((R ^ k - a ^ k) / (R - a))
          = (c * R / (R - a)) * (R ^ k - a ^ k) := by ring
        _ ≤ (c * R / (R - a)) * R ^ k := mul_le_mul_of_nonneg_left hdiff hfac
        _ = c * R * R ^ k / (R - a) := by ring
    have heq2 : (T 0 + c * R / (R - a)) * R ^ k
        = T 0 * R ^ k + c * R * R ^ k / (R - a) := by ring
    rw [heq2]
    linarith
  have hlower : c * R ^ k ≤ T k := by
    have hrec2 : ∀ k : ℕ, T (k + 1) = a * T k + (fun j => c * b ^ (d * j)) (k + 1) := hrec
    have hRt := divide_and_conquer_recursion_tree T (fun j => c * b ^ (d * j)) a hrec2
    rw [hRt k]
    have hmem : k ∈ Finset.Icc 1 k := Finset.mem_Icc.mpr ⟨hk, le_refl k⟩
    have hnonneg : ∀ j ∈ Finset.Icc 1 k, 0 ≤ a ^ (k - j) * (c * b ^ (d * j)) := by
      intro j hj
      exact mul_nonneg (pow_nonneg ha _) (mul_nonneg hc (pow_nonneg (le_of_lt hb0) _))
    have hsingle := Finset.single_le_sum hnonneg hmem
    have hterm : a ^ (k - k) * (c * b ^ (d * k)) = c * R ^ k := by
      rw [Nat.sub_self, pow_zero, one_mul, pow_mul, ← hR]
    rw [hterm] at hsingle
    have hbase : 0 ≤ a ^ k * T 0 := mul_nonneg (pow_nonneg ha k) hT0
    linarith
  exact ⟨hlower, hupper⟩
