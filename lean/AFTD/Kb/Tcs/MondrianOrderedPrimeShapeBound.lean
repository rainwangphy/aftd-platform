import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianPrimePairEncoding

/-!
# mondrian_ordered_prime_shape_bound

Topic: combinatorics   Node: 89b15257e822

Provenance: helper lemma. Helper for OP-280 and mondrian_perfect_partition_large_prime_iff. Related work: arXiv:2610.19193, Section 1 (perfect partitions and scaling); arXiv:2007.09639, Theorem 4.1 (available shapes and prime-power exclusions).

The number of ordered shapes of area A fitting in a c times p to the e square is at most the p-adic exponent of k plus one, times the number of divisors of the p-free part of A, when k times A is the square area and p exceeds c.
-/

theorem mondrian_ordered_prime_shape_bound (c p e k A : ℕ) (hc : 0 < c)
    (hp : Nat.Prime p) (hpc : c < p) (hk : 0 < k) (hA : 0 < A)
    (heq : k * A = (c * p ^ e) ^ 2) :
    (A.divisorsAntidiagonal.filter (fun d => d.1 ≤ c * p ^ e ∧ d.2 ≤ c * p ^ e)).card ≤
      (k.factorization p + 1) * (A / p ^ (A.factorization p)).divisors.card := by
  let f := fun d : ℕ × ℕ => (d.1.factorization p, d.1 / p ^ (d.1.factorization p))
  let S := A.divisorsAntidiagonal.filter (fun d => d.1 ≤ c * p ^ e ∧ d.2 ≤ c * p ^ e)
  have hmap : Set.MapsTo f ↑S
      ↑(Finset.Icc (e - k.factorization p) e ×ˢ (A / p ^ (A.factorization p)).divisors) := by
    intro d hd
    obtain ⟨hdA, hxn, hyn⟩ := Finset.mem_filter.mp hd
    have hprod := (Nat.mem_divisorsAntidiagonal.mp hdA).1
    have hx : 0 < d.1 := Nat.pos_of_mul_pos_right (by omega : 0 < d.1 * d.2)
    have hy : 0 < d.2 := Nat.pos_of_mul_pos_left (by omega : 0 < d.1 * d.2)
    obtain ⟨hlo, hup, hmem⟩ := mondrian_prime_pair_encoding c p e k A d.1 d.2
      hc hp hpc hk hA heq hx hy hxn hyn hprod
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hlo, hup⟩, hmem⟩
  have hinj : Set.InjOn f ↑S := by
    intro x hx y hy he
    have hw := congrArg (fun z : ℕ × ℕ => p ^ z.1 * z.2) he
    dsimp [f] at hw
    simp only [Nat.ordProj_mul_ordCompl_eq_self] at hw
    have hxp := (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_filter.mp hx).1).1
    have hyp := (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_filter.mp hy).1).1
    have hxpos : 0 < x.1 := Nat.pos_of_mul_pos_right (by omega : 0 < x.1 * x.2)
    apply Prod.ext hw
    apply Nat.eq_of_mul_eq_mul_left hxpos
    rw [hxp, hw, hyp]
  have hcard := Finset.card_le_card_of_injOn f hmap hinj
  calc
    S.card ≤ (Finset.Icc (e - k.factorization p) e ×ˢ
        (A / p ^ (A.factorization p)).divisors).card := hcard
    _ = (e + 1 - (e - k.factorization p)) *
        (A / p ^ (A.factorization p)).divisors.card := by simp
    _ ≤ (k.factorization p + 1) * (A / p ^ (A.factorization p)).divisors.card :=
      Nat.mul_le_mul_right _ (by omega)
