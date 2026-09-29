import AFTD.Prelude

/-!
# schwartz_zippel_zero_count_le

Topic: randomness   Node: a117bc1a6ce1

Let F be an integral domain, S a nonempty finite subset of F, n a positive integer, and p a nonzero polynomial in n variables over F of total degree d. Then the number of points x of S^n at which p vanishes is at most d·|S|^(n−1); equivalently, the fraction of the points of S^n at which p vanishes is at most d/|S|.
-/

open scoped Finset in
/-- Counting form of the Schwartz–Zippel lemma: a nonzero polynomial of total degree d vanishes on at most d·|S|^(n−1) points of S^n. -/
theorem schwartz_zippel_zero_count_le {F : Type*} [CommRing F] [IsDomain F] [DecidableEq F]
    {n : ℕ} (hn : 0 < n) {p : MvPolynomial (Fin n) F} (hp : p ≠ 0) {S : Finset F}
    (hS : 0 < S.card) :
    #{x ∈ Fintype.piFinset (fun _ : Fin n => S) | MvPolynomial.eval x p = 0}
      ≤ p.totalDegree * S.card ^ (n - 1) := by
  have hsz := MvPolynomial.schwartz_zippel_totalDegree (n := n) hp S
  have hcpos : (0 : ℚ≥0) < (S.card : ℚ≥0) := by exact_mod_cast hS
  have hcne : (S.card : ℚ≥0) ≠ 0 := hcpos.ne'
  have hcpowpos : (0 : ℚ≥0) < (S.card : ℚ≥0) ^ n := pow_pos hcpos n
  have hcpowne : (S.card : ℚ≥0) ^ n ≠ 0 := hcpowpos.ne'
  have hmul := mul_le_mul_of_nonneg_right hsz (le_of_lt hcpowpos)
  rw [div_mul_cancel₀ _ hcpowne] at hmul
  have hpow : (↑S.card : ℚ≥0) ^ n = (↑S.card : ℚ≥0) ^ (n - 1) * ↑S.card := by
    conv_lhs => rw [← Nat.sub_add_cancel hn]
    rw [pow_succ]
  have hrewrite : (↑p.totalDegree / (↑S.card : ℚ≥0)) * (↑S.card : ℚ≥0) ^ n
      = (↑(p.totalDegree * S.card ^ (n - 1)) : ℚ≥0) := by
    rw [Nat.cast_mul, Nat.cast_pow, hpow,
        mul_comm ((↑S.card : ℚ≥0) ^ (n - 1)) (↑S.card), ← mul_assoc,
        div_mul_cancel₀ _ hcne]
  rw [hrewrite] at hmul
  exact_mod_cast hmul
