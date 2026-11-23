import AFTD.Prelude
import AFTD.Kb.Tcs.TwistedFrobeniusMap

/-!
# twisted_frobenius_bijective

Topic: combinatorics   Node: 1af00c6d0f18

Provenance: helper lemma. scout/2611-17378-a-19-5-lower-bound-for-the-four-dimensional-erd-h-o-s-box-p.md:125

Let $k$ be a finite field of characteristic 2 and $K$ a degree-3 extension of $k$. Then the twisted Frobenius map $Q(x) = x^{q^2+q}$ is bijective on $K$, where $q = |k|$.
-/

lemma twisted_frobenius_bijective_coprime (q : ℕ) (h2 : 2 ∣ q) (hq : 1 ≤ q) :
    Nat.Coprime (q ^ 2 + q) (q ^ 3 - 1) := by
  have hq3_ge : 1 ≤ q ^ 3 := Nat.one_le_pow 3 q (by omega)
  have hgcd_dvd : (q ^ 2 + q).gcd (q ^ 3 - 1) ∣ 2 := by
    have h1 : ((q ^ 2 + q).gcd (q ^ 3 - 1) : ℤ) ∣ ((q : ℤ) ^ 2 + (q : ℤ)) := by
      have := Nat.gcd_dvd_left (q ^ 2 + q) (q ^ 3 - 1)
      exact_mod_cast this
    have h2 : ((q ^ 2 + q).gcd (q ^ 3 - 1) : ℤ) ∣ ((q : ℤ) ^ 3 - 1) := by
      have := Nat.gcd_dvd_right (q ^ 2 + q) (q ^ 3 - 1)
      have hcast : ((q ^ 3 - 1 : ℕ) : ℤ) = (q : ℤ) ^ 3 - 1 := by
        exact Nat.cast_sub hq3_ge
      rw [← hcast]
      exact_mod_cast this
    have hid : (2 : ℤ) = ((q : ℤ) ^ 2 + (q : ℤ) - 1) * ((q : ℤ) ^ 2 + (q : ℤ)) - ((q : ℤ) + 2) * ((q : ℤ) ^ 3 - 1) := by ring
    have hdvd_int : ((q ^ 2 + q).gcd (q ^ 3 - 1) : ℤ) ∣ 2 := by
      rw [hid]
      exact dvd_sub (dvd_mul_of_dvd_right h1 _) (dvd_mul_of_dvd_right h2 _)
    exact_mod_cast hdvd_int
  have hodd : ¬ 2 ∣ (q ^ 3 - 1) := by
    intro hc
    have hq3 : 2 ∣ q ^ 3 := dvd_pow h2 (by decide)
    rcases hq3 with ⟨a, ha⟩
    rcases hc with ⟨b, hb⟩
    have : 2 * a - 2 * b = 1 := by omega
    omega
  have hgcd_odd : ¬ 2 ∣ (q ^ 2 + q).gcd (q ^ 3 - 1) := by
    intro hc
    exact hodd (dvd_trans hc (Nat.gcd_dvd_right _ _))
  have hle : (q ^ 2 + q).gcd (q ^ 3 - 1) ≤ 2 := Nat.le_of_dvd (by decide) hgcd_dvd
  have hpos : 0 < (q ^ 2 + q).gcd (q ^ 3 - 1) := by
    refine Nat.gcd_pos_of_pos_right _ ?_
    omega
  omega

/-- The twisted Frobenius map Q permutes K = GF(q^3). -/
theorem twisted_frobenius_bijective
    (k K : Type*) [Field k] [Fintype k] [Field K] [Fintype K] [Algebra k K] [FiniteDimensional k K] [CharP k 2]
    (hrank : Module.finrank k K = 3) :
    Function.Bijective (twisted_frobenius_map (Fintype.card k) : K → K) := by
  rw [← Finite.injective_iff_bijective]
  set q := Fintype.card k
  have hq_pos : 1 ≤ q := by
    have := Fintype.one_lt_card (α := k)
    omega
  have h2 : 2 ∣ q := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [← prime_dvd_char_iff_dvd_card 2, ringChar.eq k 2]
  have hcop : Nat.Coprime (Nat.card Kˣ) (q ^ 2 + q) := by
    have hcard : Nat.card Kˣ = q ^ 3 - 1 := by
      rw [Nat.card_units, Nat.card_eq_fintype_card, @Module.card_eq_pow_finrank k K, hrank]
    rw [hcard]
    exact (twisted_frobenius_bijective_coprime q h2 hq_pos).symm
  intro x y hxy
  change x ^ (q ^ 2 + q) = y ^ (q ^ 2 + q) at hxy
  by_cases hx : x = 0
  · subst hx
    rw [zero_pow (by omega)] at hxy
    exact (eq_zero_of_pow_eq_zero hxy.symm).symm
  · by_cases hy : y = 0
    · subst hy
      rw [zero_pow (by omega)] at hxy
      exact eq_zero_of_pow_eq_zero hxy
    · have hpow : (Units.mk0 x hx) ^ (q ^ 2 + q) = (Units.mk0 y hy) ^ (q ^ 2 + q) := by
        apply Units.ext
        simp [hxy]
      have hinj : (powCoprime hcop) (Units.mk0 x hx) = (powCoprime hcop) (Units.mk0 y hy) := by
        rw [powCoprime_apply, powCoprime_apply]
        exact hpow
      have heq : Units.mk0 x hx = Units.mk0 y hy := (powCoprime hcop).injective hinj
      exact congr_arg Units.val heq
