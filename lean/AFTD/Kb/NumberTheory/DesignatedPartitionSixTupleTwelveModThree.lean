import AFTD.Prelude
import AFTD.Kb.NumberTheory.DesignatedPartitionKTuple
import AFTD.Kb.Tcs.Monomial
import AFTD.Kb.NumberTheory.DesignatedPartitionGenFun

/-!
# designated_partition_six_tuple_twelve_mod_three

Topic: elementary_number_theory   Node: 7119fce18a7d

Provenance: formalization of a published result. Source: arXiv:2611.05623 Theorem 3.1

For every natural number n, 3 divides the number of designated partition 6-tuples of size 12n + 10, designated_partition_k_tuple 6 (12 * n + 10).
-/

private lemma designated_partition_six_tuple_twelve_mod_three_aux (n : ℕ) :
    3 ∣ designated_partition_k_tuple 6 (12 * n + 10) := by
  have hpoly : ∀ P : Polynomial (ZMod 3), P ^ 3 = Polynomial.expand (ZMod 3) 3 P := by
    intro P
    induction P using Polynomial.induction_on' with
    | add p q hp hq => rw [add_pow_char, hp, hq, map_add]
    | monomial k a =>
      rw [Polynomial.expand_monomial]
      rw [show Polynomial.monomial k a = Polynomial.C a * Polynomial.X ^ k from
        (Polynomial.C_mul_X_pow_eq_monomial).symm]
      rw [mul_pow, ← Polynomial.C_pow, ← pow_mul, ZMod.pow_card,
        Polynomial.C_mul_X_pow_eq_monomial]
  have hcoeff : ∀ (f : PowerSeries (ZMod 3)) (m : ℕ), ¬ 3 ∣ m → (f ^ 3).coeff m = 0 := by
    intro f m hm
    rw [(PowerSeries.coeff_coe_trunc_of_lt (n := m) (m := m+1) (f := f^3)
      (show m < m+1 by omega)).symm]
    rw [← PowerSeries.trunc_trunc_pow f (m+1) 3]
    rw [PowerSeries.coeff_coe_trunc_of_lt (n := m) (m := m+1)
      (f := ((PowerSeries.trunc (m+1) f : PowerSeries (ZMod 3)) ^ 3))
      (show m < m+1 by omega)]
    rw [← Polynomial.coe_pow, Polynomial.coeff_coe, hpoly]
    rw [Polynomial.coeff_expand (by norm_num), if_neg hm]
  set m := 12 * n + 10
  have hm : ¬ 3 ∣ m := by omega
  have key : ((designated_partition_k_tuple 6 m : ℕ) : ZMod 3) =
      (PowerSeries.coeff m)
        (PowerSeries.map (Nat.castRingHom (ZMod 3)) (designated_partition_gen_fun ^ 6)) := by
    rw [PowerSeries.coeff_map]
    rfl
  have hN : ((designated_partition_k_tuple 6 m : ℕ) : ZMod 3) = 0 := by
    rw [key]
    rw [show designated_partition_gen_fun ^ 6 = (designated_partition_gen_fun ^ 2) ^ 3 by ring]
    rw [map_pow]
    rw [hcoeff _ m hm]
  exact (ZMod.natCast_eq_zero_iff (designated_partition_k_tuple 6 m) 3).1 hN

/-- For all natural numbers n, 3 divides the number of designated partition 6-tuples of size 12n + 10. -/
theorem designated_partition_six_tuple_twelve_mod_three (n : ℕ) :
    3 ∣ designated_partition_k_tuple 6 (12 * n + 10) := designated_partition_six_tuple_twelve_mod_three_aux n
