import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianDistinctPrimeNotDvdPow
import AFTD.Kb.Tcs.MondrianFactorShapes
import AFTD.Kb.Tcs.MondrianMemFactorShapes
import AFTD.Kb.Tcs.MondrianShapeExponentIntervalBound
import AFTD.Kb.Tcs.MondrianTwoPrimeFactorPairEncoding
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# mondrian_prime_square_area_middle_shape_bound

Topic: combinatorics   Node: bf6456cefc63

Provenance: helper lemma. Helper for OP-280 and mondrian_no_perfect_prime_mul_prime_pow. Related work: arXiv:2610.19193, Section 1 (the zero-defect question); arXiv:2007.09639, Theorem 4.1 (prime-power and small prime-product exclusions).

For distinct primes p and q and t+r=2e with positive r, at most r unordered shapes of area q^2 times p^t fitting in a q times p^e square have both sides divisible by q.
-/

theorem mondrian_prime_square_area_middle_shape_bound (p q e t r : ℕ) (hp : Nat.Prime p)
    (hq : Nat.Prime q) (hpq : p ≠ q) (htr : t + r = 2 * e) (hr : 0 < r) :
    ((mondrian_factor_shapes (q * p ^ e) (q ^ 2 * p ^ t)).filter
      (fun d => q ∣ d.1 ∧ q ∣ d.2)).card ≤ r := by
  have hp0 := hp.pos
  have hq0 := hq.pos
  let S := (mondrian_factor_shapes (q * p ^ e) (q ^ 2 * p ^ t)).filter
    (fun d => q ∣ d.1 ∧ q ∣ d.2)
  have he : 0 < e := by omega
  have hdata : ∀ d ∈ S, d.1 = q * p ^ d.1.factorization p ∧
      d.2 = q * p ^ d.2.factorization p ∧
      d.1.factorization p + d.2.factorization p = t ∧
      d.1.factorization p ≤ d.2.factorization p ∧ d.2.factorization p ≤ e := by
    intro d hd
    obtain ⟨hdS, hdivx, hdivy⟩ := Finset.mem_filter.mp hd
    obtain ⟨hprod, _, hord, hn⟩ := (mondrian_mem_factor_shapes _ _ d).mp hdS
    have hx : 0 < d.1 := Nat.pos_of_mul_pos_right (by rw [hprod]; positivity)
    have hy : 0 < d.2 := Nat.pos_of_mul_pos_left (by rw [hprod]; positivity)
    obtain ⟨b, c, hbc, hxb, hyc, hv⟩ := mondrian_two_prime_factor_pair_encoding p q t 2 d.1 d.2
      hp hq hpq hx hy hprod
    have hb : b ≠ 0 := by
      intro hh
      have hnod := mondrian_distinct_prime_not_dvd_pow p q (d.1.factorization p) hp hq hpq
      apply hnod
      rw [hxb, hh, pow_zero, one_mul] at hdivx
      exact hdivx
    have hc : c ≠ 0 := by
      intro hh
      have hnod := mondrian_distinct_prime_not_dvd_pow p q (d.2.factorization p) hp hq hpq
      apply hnod
      rw [hyc, hh, pow_zero, one_mul] at hdivy
      exact hdivy
    have hb1 : b = 1 := by omega
    have hc1 : c = 1 := by omega
    simp only [hb1, hc1, pow_one] at hxb hyc
    have hab : d.1.factorization p ≤ d.2.factorization p := by
      apply (Nat.pow_le_pow_iff_right hp.one_lt).mp
      rw [hxb, hyc] at hord
      nlinarith [hq.pos]
    have hbe : d.2.factorization p ≤ e := by
      apply (Nat.pow_le_pow_iff_right hp.one_lt).mp
      rw [hyc] at hn
      nlinarith [hq.pos]
    exact ⟨hxb, hyc, hv, hab, hbe⟩
  have hh := mondrian_shape_exponent_interval_bound p (q * p ^ e) (q ^ 2 * p ^ t) q
    (e - r) (e - 1) S (Nat.mul_pos (pow_pos hq.pos 2) (pow_pos hp.pos t)) (fun _ h => (Finset.mem_filter.mp h).1)
    Prod.fst (fun d => d.1.factorization p)
    (by intro d hd; exact ⟨Or.inl rfl, (hdata d hd).1⟩) (by
      intro d hd
      obtain ⟨_, _, hv, hab, hbe⟩ := hdata d hd
      constructor <;> omega)
  dsimp [S] at hh
  omega
