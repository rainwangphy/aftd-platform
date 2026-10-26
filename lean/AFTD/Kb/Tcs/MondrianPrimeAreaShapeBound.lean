import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianDistinctPrimeNotDvdPow
import AFTD.Kb.Tcs.MondrianFactorShapes
import AFTD.Kb.Tcs.MondrianMemFactorShapes
import AFTD.Kb.Tcs.MondrianPrimeFreeFactorPairEncoding
import AFTD.Kb.Tcs.MondrianPrimePowerSideLogBound
import AFTD.Kb.Tcs.MondrianShapeExponentIntervalBound
import AFTD.Kb.Tcs.MondrianTwoPrimeFactorPairEncoding
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# mondrian_prime_area_shape_bound

Topic: combinatorics   Node: 32f1c12f373e

Provenance: helper lemma. Helper for OP-280 and mondrian_no_perfect_prime_mul_prime_pow. Related work: arXiv:2610.19193, Section 1 (the zero-defect question); arXiv:2007.09639, Theorem 4.1 (prime-power and small prime-product exclusions).

For distinct primes p and q, if t+r=2e, at most r plus floor(log_p(q)) plus one shapes of area q times p^t fit in the q times p^e square.
-/

theorem mondrian_prime_area_shape_bound (p q e t r : ℕ) (hp : Nat.Prime p)
    (hq : Nat.Prime q) (hpq : p ≠ q) (htr : t + r = 2 * e) :
    (mondrian_factor_shapes (q * p ^ e) (q * p ^ t)).card ≤ r + Nat.log p q + 1 := by
  let S := mondrian_factor_shapes (q * p ^ e) (q * p ^ t)
  let g := fun d : ℕ × ℕ => if q ∣ d.1 then d.2 else d.1
  let o := fun d : ℕ × ℕ => if q ∣ d.1 then d.1 else d.2
  let f := fun d => (g d).factorization p
  have hg : ∀ d ∈ S, (g d = d.1 ∨ g d = d.2) ∧
      g d = p ^ f d ∧ o d = q * p ^ ((o d).factorization p) ∧
      f d + (o d).factorization p = t ∧ g d ≤ q * p ^ e ∧ o d ≤ q * p ^ e := by
    intro d hd
    obtain ⟨hprod, _, hord, hn⟩ := (mondrian_mem_factor_shapes _ _ d).mp hd
    have hx : 0 < d.1 := Nat.pos_of_mul_pos_right (by rw [hprod]; exact Nat.mul_pos hq.pos (pow_pos hp.pos t))
    have hy : 0 < d.2 := Nat.pos_of_mul_pos_left (by rw [hprod]; exact Nat.mul_pos hq.pos (pow_pos hp.pos t))
    have hfree : ¬ q ∣ d.1 ∨ ¬ q ∣ d.2 := by
      obtain ⟨b, c, hbc, hxb, hyc, hv⟩ := mondrian_two_prime_factor_pair_encoding p q t 1 d.1 d.2
        hp hq hpq hx hy (by simpa using hprod)
      have hbc' : b = 0 ∨ c = 0 := by omega
      rcases hbc' with hb | hc
      · left
        rw [hxb, hb, pow_zero, one_mul]
        exact mondrian_distinct_prime_not_dvd_pow p q (d.1.factorization p) hp hq hpq
      · right
        rw [hyc, hc, pow_zero, one_mul]
        exact mondrian_distinct_prime_not_dvd_pow p q (d.2.factorization p) hp hq hpq
    by_cases hh : q ∣ d.1
    · have hfree' : ¬ q ∣ d.2 := hfree.resolve_left (by simpa using hh)
      have h := mondrian_prime_free_factor_pair_encoding p q t 1 d.2 d.1 hp hq hpq hy hx
        (by simpa [Nat.mul_comm] using hprod) hfree'
      simpa [g, o, f, hh] using And.intro (Or.inr rfl : d.2 = d.1 ∨ d.2 = d.2)
        (And.intro h.1 (And.intro h.2.1 (And.intro h.2.2 (And.intro hn (hord.trans hn)))))
    · have h := mondrian_prime_free_factor_pair_encoding p q t 1 d.1 d.2 hp hq hpq hx hy
        (by simpa using hprod) hh
      simpa [g, o, f, hh] using And.intro (Or.inl rfl : d.1 = d.1 ∨ d.1 = d.2)
        (And.intro h.1 (And.intro h.2.1 (And.intro h.2.2 (And.intro (hord.trans hn) hn))))
  have hh := mondrian_shape_exponent_interval_bound p (q * p ^ e) (q * p ^ t) 1
    (e - r) (e + Nat.log p q) S (Nat.mul_pos hq.pos (pow_pos hp.pos t))
    (fun _ h => h) g f (by intro d hd; exact ⟨(hg d hd).1, by simpa using (hg d hd).2.1⟩) (by
      intro d hd
      obtain ⟨_, hgp, hop, hv, hgn, hon⟩ := hg d hd
      have ha := mondrian_prime_power_side_log_bound p q e (f d) hp (by rwa [← hgp])
      have hb : (o d).factorization p ≤ e := by
        apply (Nat.pow_le_pow_iff_right hp.one_lt).mp
        have := hon
        rw [hop] at this
        nlinarith [hq.pos]
      constructor <;> omega)
  dsimp [S] at hh
  omega
