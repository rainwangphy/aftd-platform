import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianDvdPrimePowEq
import AFTD.Kb.Tcs.MondrianFactorShapes
import AFTD.Kb.Tcs.MondrianMemFactorShapes
import AFTD.Kb.Tcs.MondrianPrimePowerSideLogBound
import AFTD.Kb.Tcs.MondrianShapeExponentIntervalBound
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# mondrian_prime_free_area_shape_bound

Topic: combinatorics   Node: 566269c053db

Provenance: helper lemma. Helper for OP-280 and mondrian_no_perfect_prime_mul_prime_pow. Related work: arXiv:2610.19193, Section 1 (the zero-defect question); arXiv:2007.09639, Theorem 4.1 (prime-power and small prime-product exclusions).

For distinct primes p and q, if t+r=2e, at most r plus floor(log_p(q)) plus one shapes of pure p-power area p^t fit in the q times p^e square.
-/

theorem mondrian_prime_free_area_shape_bound (p q e t r : ℕ) (hp : Nat.Prime p)
    (hq : Nat.Prime q) (hpq : p ≠ q) (htr : t + r = 2 * e) :
    (mondrian_factor_shapes (q * p ^ e) (p ^ t)).card ≤ r + Nat.log p q + 1 := by
  let S := mondrian_factor_shapes (q * p ^ e) (p ^ t)
  have hpow : ∀ d ∈ S, d.1 = p ^ d.1.factorization p ∧
      d.2 = p ^ d.2.factorization p ∧ d.1.factorization p + d.2.factorization p = t := by
    intro d hd
    obtain ⟨hprod, _, hord, hn⟩ := (mondrian_mem_factor_shapes _ _ d).mp hd
    have hx : 0 < d.1 := Nat.pos_of_mul_pos_right (by rw [hprod]; exact pow_pos hp.pos t)
    have hy : 0 < d.2 := Nat.pos_of_mul_pos_left (by rw [hprod]; exact pow_pos hp.pos t)
    have hxpow := mondrian_dvd_prime_pow_eq p t d.1 hp ⟨d.2, hprod.symm⟩
    have hypow := mondrian_dvd_prime_pow_eq p t d.2 hp ⟨d.1, by nlinarith [hprod]⟩
    have hh := congrArg (fun z : ℕ => z.factorization p) hprod
    have hv : d.1.factorization p + d.2.factorization p = t := by
      simpa [Nat.factorization_mul (by omega : d.1 ≠ 0) (by omega : d.2 ≠ 0),
        Nat.factorization_pow_self hp, hp.factorization_self] using hh
    exact ⟨hxpow, hypow, hv⟩
  have hh := mondrian_shape_exponent_interval_bound p (q * p ^ e) (p ^ t) 1
    (e - r - Nat.log p q) e S (pow_pos hp.pos t) (fun _ h => h)
    Prod.fst (fun d => d.1.factorization p) (by
      intro d hd
      exact ⟨Or.inl rfl, by simpa using (hpow d hd).1⟩) (by
      intro d hd
      obtain ⟨hprod, _, hord, hn⟩ := (mondrian_mem_factor_shapes _ _ d).mp hd
      obtain ⟨hxpow, hypow, hv⟩ := hpow d hd
      have hb : d.2.factorization p ≤ e + Nat.log p q :=
        mondrian_prime_power_side_log_bound p q e _ hp (by simpa [← hypow] using hn)
      have hab : d.1.factorization p ≤ d.2.factorization p :=
        (Nat.pow_le_pow_iff_right hp.one_lt).mp (by simpa [← hxpow, ← hypow] using hord)
      constructor <;> omega)
  dsimp [S] at hh
  omega
