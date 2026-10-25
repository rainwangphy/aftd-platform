import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianDvdPrimePowEq
import AFTD.Kb.Tcs.MondrianFactorShapes
import AFTD.Kb.Tcs.MondrianMemFactorShapes
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# mondrian_prime_power_shape_bound

Topic: combinatorics   Node: 8e919563b267

Provenance: helper lemma. Helper for OP-280 and mondrian_perfect_partition_large_prime_iff. Related work: arXiv:2610.19193, Section 1 (perfect partitions and scaling); arXiv:2007.09639, Theorem 4.1 (available shapes and prime-power exclusions).

For k at least two and positive A with k times A equal to the area of a p-power square, the number of available shapes is at most the p-adic exponent of k.
-/

theorem mondrian_prime_power_shape_bound (p e k A : ℕ) (hp : Nat.Prime p)
    (hk : 2 ≤ k) (hA : 0 < A) (heq : k * A = (p ^ e) ^ 2) :
    (mondrian_factor_shapes (p ^ e) A).card ≤ k.factorization p := by
  have hkne : k ≠ 0 := by omega
  have hAne : A ≠ 0 := by omega
  have hnne : p ^ e ≠ 0 := pow_ne_zero e hp.ne_zero
  have hApow : A ∣ p ^ (2 * e) := by
    have hnp : (p ^ e) ^ 2 = p ^ (2 * e) := by rw [← pow_mul, Nat.mul_comm e 2]
    rw [← hnp, ← heq]
    exact dvd_mul_left A k
  have hvals : k.factorization p + A.factorization p = 2 * e := by
    have hf := congrArg (fun z : ℕ => z.factorization p) heq
    rw [Nat.factorization_mul hkne hAne, Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      Nat.factorization_pow_self hp] at hf
    exact hf
  let f := fun d : ℕ × ℕ => d.1.factorization p
  have hmap : Set.MapsTo f ↑(mondrian_factor_shapes (p ^ e) A)
      ↑(Finset.Ico (e - k.factorization p) e) := by
    intro d hd
    obtain ⟨hprod, _, hord, hn⟩ := (mondrian_mem_factor_shapes (p ^ e) A d).mp hd
    have hx : 0 < d.1 := Nat.pos_of_mul_pos_right (by omega : 0 < d.1 * d.2)
    have hy : 0 < d.2 := Nat.pos_of_mul_pos_left (by omega : 0 < d.1 * d.2)
    have hxdvd : d.1 ∣ p ^ (2 * e) := (Dvd.intro d.2 hprod).trans hApow
    have hydvd : d.2 ∣ p ^ (2 * e) := by
      apply dvd_trans _ hApow
      exact ⟨d.1, by nlinarith [hprod]⟩
    have hxpow := mondrian_dvd_prime_pow_eq p (2 * e) d.1 hp hxdvd
    have hypow := mondrian_dvd_prime_pow_eq p (2 * e) d.2 hp hydvd
    have hxlt : d.1 < p ^ e := by
      have hAlt : A < (p ^ e) ^ 2 := by nlinarith
      by_contra hnot
      have hle : p ^ e ≤ d.1 := by omega
      have hmul := Nat.mul_le_mul hle (hle.trans hord)
      nlinarith
    have hxe : d.1.factorization p < e := by
      apply (Nat.pow_lt_pow_iff_right hp.one_lt).mp
      simpa only [← hxpow] using hxlt
    have hye : d.2.factorization p ≤ e := by
      apply (Nat.pow_le_pow_iff_right hp.one_lt).mp
      simpa only [← hypow] using hn
    have hxyval : d.1.factorization p + d.2.factorization p = A.factorization p := by
      have hh := congrArg (fun z : ℕ => z.factorization p) hprod
      simpa only [Nat.factorization_mul (Nat.ne_of_gt hx) (Nat.ne_of_gt hy),
        Finsupp.add_apply] using hh
    simp only [f, Finset.mem_coe, Finset.mem_Ico]
    omega
  have hinj : Set.InjOn f ↑(mondrian_factor_shapes (p ^ e) A) := by
    intro x hx y hy hxy
    obtain ⟨hxp, _, _, _⟩ := (mondrian_mem_factor_shapes (p ^ e) A x).mp hx
    obtain ⟨hyp, _, _, _⟩ := (mondrian_mem_factor_shapes (p ^ e) A y).mp hy
    have hxdvd : x.1 ∣ p ^ (2 * e) := (Dvd.intro x.2 hxp).trans hApow
    have hydvd : y.1 ∣ p ^ (2 * e) := (Dvd.intro y.2 hyp).trans hApow
    have hw : x.1 = y.1 := by
      rw [mondrian_dvd_prime_pow_eq p (2 * e) x.1 hp hxdvd,
        mondrian_dvd_prime_pow_eq p (2 * e) y.1 hp hydvd]
      exact congrArg (fun u => p ^ u) hxy
    have hxpos : 0 < x.1 := Nat.pos_of_mul_pos_right (by omega : 0 < x.1 * x.2)
    apply Prod.ext hw
    apply Nat.eq_of_mul_eq_mul_left hxpos
    rw [hxp, hw, hyp]
  have hc := Finset.card_le_card_of_injOn f hmap hinj
  have hcard : (Finset.Ico (e - k.factorization p) e).card ≤ k.factorization p := by
    simp only [Nat.card_Ico]
    omega
  exact hc.trans hcard
