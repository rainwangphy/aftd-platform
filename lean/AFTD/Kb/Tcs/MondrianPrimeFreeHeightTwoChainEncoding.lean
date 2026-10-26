import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianTwoPrimeDivisorEncoding
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# mondrian_prime_free_height_two_chain_encoding

Topic: combinatorics   Node: 5d33a6a2cb0f

Provenance: helper lemma. For the three-prime extension of OP-280, arXiv:2610.19193, Section 1. This develops the proved mondrian_no_perfect_two_prime_area and the width-free signed-height relation from this session.

If x*y=q^s*r*p^a for primes p,q,r with p≠r, and q does not divide x, then y lies in one of the chains q^s*p^b or q^s*r*p^b.
-/

theorem mondrian_prime_free_height_two_chain_encoding (p q r a s x y : ℕ)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hr : Nat.Prime r) (hpr : p ≠ r)
    (hxy : x * y = q ^ s * r * p ^ a) (hx : ¬ q ∣ x) :
    ∃ b : ℕ, y = q ^ s * p ^ b ∨ y = q ^ s * r * p ^ b := by
  have hcop : (q ^ s).Coprime x := (hq.coprime_iff_not_dvd.mpr hx).pow_left s
  have hy : q ^ s ∣ y := hcop.dvd_mul_left.mp (by
    rw [hxy]
    exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _)
  obtain ⟨z, hz⟩ := hy
  have hprod : x * z = r * p ^ a := by
    rw [hz] at hxy
    apply Nat.eq_of_mul_eq_mul_left (pow_pos hq.pos s)
    nlinarith [hxy]
  have hzdiv : z ∣ r ^ 1 * p ^ a := by
    rw [pow_one]
    exact ⟨x, by nlinarith [hprod]⟩
  obtain ⟨b, hb, hzb⟩ := mondrian_two_prime_divisor_encoding p r a 1 z hp hr hpr hzdiv
  refine ⟨z.factorization p, ?_⟩
  have hbcase : b = 0 ∨ b = 1 := by omega
  rcases hbcase with rfl | rfl
  · left
    simpa only [pow_zero, one_mul] using hz.trans (congrArg (fun v => q ^ s * v) hzb)
  · right
    simpa only [pow_one, Nat.mul_assoc] using hz.trans (congrArg (fun v => q ^ s * v) hzb)
