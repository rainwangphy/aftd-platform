import AFTD.Prelude

/-!
# schwartz_zippel_exists_nonzero_eval

Topic: randomness   Node: 92be20caee7c

Let F be an integral domain, p a nonzero polynomial in n variables over F, and S a nonempty finite subset of F. If the total degree of p is less than the cardinality of S, then there is a point x in S^n at which p does not vanish. Equivalently, a nonzero polynomial of total degree d is not the zero function on S^n, so random evaluation from S^n detects nonzeroness.
-/

/-- Schwartz–Zippel, PIT form: a nonzero polynomial of total degree < |S| has a nonvanishing point in S^n. -/
theorem schwartz_zippel_exists_nonzero_eval {F : Type*} [CommRing F] [IsDomain F] [DecidableEq F]
    {n : ℕ} {p : MvPolynomial (Fin n) F} (hp : p ≠ 0) {S : Finset F} (hS : 0 < S.card)
    (hd : p.totalDegree < S.card) :
    ∃ x ∈ Fintype.piFinset (fun _ : Fin n => S), MvPolynomial.eval x p ≠ 0 := by
  by_contra h
  push Not at h
  have hcard : ((Fintype.piFinset (fun _ : Fin n => S)).filter
      (fun f => MvPolynomial.eval f p = 0)).card = S.card ^ n := by
    rw [Finset.filter_true_of_mem]
    · exact Fintype.card_piFinset_const S n
    · intro x hx; exact h x hx
  have hsz := MvPolynomial.schwartz_zippel_totalDegree (n := n) hp S
  rw [hcard] at hsz
  have hc : (0 : ℚ≥0) < S.card := by exact_mod_cast hS
  have hcpow : ((S.card : ℚ≥0)) ^ n ≠ 0 := pow_ne_zero _ hc.ne'
  have hle1 : (1 : ℚ≥0) ≤ (p.totalDegree : ℚ≥0) / S.card := by
    have h_eq : ((S.card ^ n : ℕ) : ℚ≥0) / ((S.card : ℚ≥0) ^ n) = 1 := by
      rw [Nat.cast_pow, div_self hcpow]
    rwa [h_eq] at hsz
  have hle2 : (S.card : ℚ≥0) ≤ (p.totalDegree : ℚ≥0) := by
    have hmul := mul_le_mul_of_nonneg_right hle1 (le_of_lt hc)
    rwa [one_mul, div_mul_cancel₀ _ hc.ne'] at hmul
  have hnat : S.card ≤ p.totalDegree := by exact_mod_cast hle2
  omega
