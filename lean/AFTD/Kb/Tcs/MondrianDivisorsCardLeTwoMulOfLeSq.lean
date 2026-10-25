import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# mondrian_divisors_card_le_two_mul_of_le_sq

Topic: combinatorics   Node: c9e4c5646785

Provenance: helper lemma. Helper for OP-280 and mondrian_perfect_partition_large_prime_iff. Related work: arXiv:2610.19193, Section 1 (perfect partitions and scaling); arXiv:2007.09639, Theorem 4.1 (available shapes and prime-power exclusions).

An integer D at most c squared has at most 2c positive divisors.
-/

theorem mondrian_divisors_card_le_two_mul_of_le_sq (D c : ℕ) (hDc : D ≤ c ^ 2) :
    D.divisors.card ≤ 2 * c := by
  by_cases hD : D = 0
  · simp [hD]
  let f := fun d : ℕ × ℕ => (min d.1 d.2, decide (d.1 ≤ d.2))
  have hmap : Set.MapsTo f ↑D.divisorsAntidiagonal
      ↑(Finset.Icc 1 c ×ˢ (Finset.univ : Finset Bool)) := by
    intro d hd
    obtain ⟨hprod, _⟩ := Nat.mem_divisorsAntidiagonal.mp hd
    have hx : 0 < d.1 := Nat.pos_of_mul_pos_right (by omega : 0 < d.1 * d.2)
    have hy : 0 < d.2 := Nat.pos_of_mul_pos_left (by omega : 0 < d.1 * d.2)
    have hmin : min d.1 d.2 ≤ c := by
      by_contra hn
      have h1 : c < d.1 := lt_of_lt_of_le (by omega : c < min d.1 d.2) (min_le_left _ _)
      have h2 : c < d.2 := lt_of_lt_of_le (by omega : c < min d.1 d.2) (min_le_right _ _)
      have hm := Nat.mul_le_mul (by omega : c + 1 ≤ d.1) (by omega : c + 1 ≤ d.2)
      nlinarith
    simp only [f, Finset.mem_coe, Finset.mem_product, Finset.mem_Icc, Finset.mem_univ,
      and_true]
    exact ⟨by omega, hmin⟩
  have hinj : Set.InjOn f ↑D.divisorsAntidiagonal := by
    intro x hx y hy he
    have hm := congrArg Prod.fst he
    have hb := congrArg Prod.snd he
    dsimp [f] at hm hb
    obtain ⟨hxp, _⟩ := Nat.mem_divisorsAntidiagonal.mp hx
    obtain ⟨hyp, _⟩ := Nat.mem_divisorsAntidiagonal.mp hy
    have hxpos : 0 < x.1 := Nat.pos_of_mul_pos_right (by omega : 0 < x.1 * x.2)
    have hypos : 0 < x.2 := Nat.pos_of_mul_pos_left (by omega : 0 < x.1 * x.2)
    by_cases hxord : x.1 ≤ x.2
    · have hyord : y.1 ≤ y.2 := by simpa [hxord] using hb.symm
      have hw : x.1 = y.1 := by simpa [min_eq_left hxord, min_eq_left hyord] using hm
      apply Prod.ext hw
      apply Nat.eq_of_mul_eq_mul_left hxpos
      rw [hxp, hw, hyp]
    · have hyord : ¬ y.1 ≤ y.2 := by simpa [hxord] using hb.symm
      have hw : x.2 = y.2 := by
        simpa [min_eq_right (by omega : x.2 ≤ x.1),
          min_eq_right (by omega : y.2 ≤ y.1)] using hm
      apply Prod.ext _ hw
      apply Nat.eq_of_mul_eq_mul_right hypos
      rw [hxp, hw, hyp]
  have hc := Finset.card_le_card_of_injOn f hmap hinj
  rw [← Nat.map_div_right_divisors, Finset.card_map] at hc
  simpa [Nat.mul_comm] using hc
