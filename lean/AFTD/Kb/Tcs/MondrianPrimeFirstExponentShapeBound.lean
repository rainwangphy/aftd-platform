import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianFactorShapes
import AFTD.Kb.Tcs.MondrianFactorizationLeScaledPrimePow
import AFTD.Kb.Tcs.MondrianMemFactorShapes
import AFTD.Kb.Tcs.MondrianSortedPairsEqOfShared
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# mondrian_prime_first_exponent_shape_bound

Topic: combinatorics   Node: fabb7fed122b

Provenance: helper lemma. Helper for OP-280 and mondrian_perfect_partition_large_prime_iff. Related work: arXiv:2610.19193, Section 1 (perfect partitions and scaling); arXiv:2007.09639, Theorem 4.1 (available shapes and prime-power exclusions).

When the p-adic exponent of k is exactly one, at most c unordered shapes of area A fit in a c times p to the e square with area k times A and p exceeding c.
-/

theorem mondrian_prime_first_exponent_shape_bound (c p e k A : ℕ) (hc : 0 < c)
    (hp : Nat.Prime p) (hpc : c < p) (hk : 0 < k) (hA : 0 < A)
    (heq : k * A = (c * p ^ e) ^ 2) (hr : k.factorization p = 1) :
    (mondrian_factor_shapes (c * p ^ e) A).card ≤ c := by
  have hcnot : ¬ p ∣ c := Nat.not_dvd_of_pos_of_lt hc hpc
  have hvals : 1 + A.factorization p = 2 * e := by
    have hf := congrArg (fun z : ℕ => z.factorization p) heq
    rw [Nat.factorization_mul (Nat.ne_of_gt hk) (Nat.ne_of_gt hA), Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      Nat.factorization_mul (Nat.ne_of_gt hc) (pow_ne_zero e hp.ne_zero), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hcnot,
      Nat.factorization_pow_self hp, hr] at hf
    simpa using hf
  let high := fun d : ℕ × ℕ => if d.1.factorization p = e then d.1 else d.2
  let f := fun d : ℕ × ℕ => high d / p ^ e
  have hhigh : ∀ d ∈ mondrian_factor_shapes (c * p ^ e) A,
      0 < high d ∧ high d ≤ c * p ^ e ∧ (high d).factorization p = e := by
    intro d hd
    obtain ⟨hprod, _, hord, hn⟩ := (mondrian_mem_factor_shapes (c * p ^ e) A d).mp hd
    have hx : 0 < d.1 := Nat.pos_of_mul_pos_right (by omega : 0 < d.1 * d.2)
    have hy : 0 < d.2 := Nat.pos_of_mul_pos_left (by omega : 0 < d.1 * d.2)
    have hxval := mondrian_factorization_le_scaled_prime_pow c p e d.1 hp hpc hx (hord.trans hn)
    have hyval := mondrian_factorization_le_scaled_prime_pow c p e d.2 hp hpc hy hn
    have hxyval : d.1.factorization p + d.2.factorization p = A.factorization p := by
      have hh := congrArg (fun z : ℕ => z.factorization p) hprod
      simpa only [Nat.factorization_mul (Nat.ne_of_gt hx) (Nat.ne_of_gt hy),
        Finsupp.add_apply] using hh
    by_cases hh : d.1.factorization p = e
    · simpa only [high, if_pos hh] using And.intro hx (And.intro (hord.trans hn) hh)
    · have hyval' : d.2.factorization p = e := by omega
      simpa only [high, if_neg hh] using And.intro hy (And.intro hn hyval')
  have hrec : ∀ d ∈ mondrian_factor_shapes (c * p ^ e) A,
      high d = p ^ e * f d := by
    intro d hd
    have hf := Nat.ordProj_mul_ordCompl_eq_self (high d) p
    rw [(hhigh d hd).2.2] at hf
    exact hf.symm
  have hmap : Set.MapsTo f ↑(mondrian_factor_shapes (c * p ^ e) A) ↑(Finset.Icc 1 c) := by
    intro d hd
    have hrec' := hrec d hd
    obtain ⟨hpos, hn, hv⟩ := hhigh d hd
    have hppos := pow_pos hp.pos e
    apply Finset.mem_Icc.mpr
    constructor
    · by_contra hn
      have hf0 : f d = 0 := by omega
      rw [hf0, Nat.mul_zero] at hrec'
      omega
    · by_contra hn
      have hm := Nat.mul_le_mul_left (p ^ e) (by omega : c + 1 ≤ f d)
      nlinarith
  have hinj : Set.InjOn f ↑(mondrian_factor_shapes (c * p ^ e) A) := by
    intro x hx y hy he
    have hg : high x = high y := by rw [hrec x hx, hrec y hy, he]
    obtain ⟨hxp, _, hxo, _⟩ := (mondrian_mem_factor_shapes (c * p ^ e) A x).mp hx
    obtain ⟨hyp, _, hyo, _⟩ := (mondrian_mem_factor_shapes (c * p ^ e) A y).mp hy
    apply mondrian_sorted_pairs_eq_of_shared x y A hA hxp hyp hxo hyo
    dsimp [high] at hg
    split_ifs at hg <;> tauto
  have hcard := Finset.card_le_card_of_injOn f hmap hinj
  simpa using hcard
