import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianDvdPrimePowEq
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# mondrian_prime_free_height_encoding

Topic: combinatorics   Node: 5a1a58eab0f4

Provenance: helper lemma. For OP-280, arXiv:2610.19193, Section 1. Related work: arXiv:2007.09639, Theorem 4.1; HAL:hal-05729522v2, Lemma 2.3 (primitive cross sections and common-side descent). The periodic residue argument and the uniform two-prime common-area exclusion are developed here.

If x*y=q^s*p^t for primes p and q and q does not divide x, then y is q^s times a power of p; the primes need not be distinct.
-/

theorem mondrian_prime_free_height_encoding (p q s t x y : ℕ) (hp : Nat.Prime p)
    (hq : Nat.Prime q) (hxy : x * y = q ^ s * p ^ t) (hx : ¬ q ∣ x) :
    ∃ a, y = q ^ s * p ^ a := by
  have hcop : (q ^ s).Coprime x := (hq.coprime_iff_not_dvd.mpr hx).pow_left s
  have hy : q ^ s ∣ y := hcop.dvd_mul_left.mp (by rw [hxy]; exact dvd_mul_right _ _)
  obtain ⟨z, hz⟩ := hy
  have hprod : x * z = p ^ t := by
    rw [hz] at hxy
    apply Nat.eq_of_mul_eq_mul_left (pow_pos hq.pos s)
    nlinarith [hxy]
  have hzpow := mondrian_dvd_prime_pow_eq p t z hp ⟨x, by nlinarith [hprod]⟩
  refine ⟨z.factorization p, ?_⟩
  rw [hz]
  exact congrArg (fun v => q ^ s * v) hzpow
