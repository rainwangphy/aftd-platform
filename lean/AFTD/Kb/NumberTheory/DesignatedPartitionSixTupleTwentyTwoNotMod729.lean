import AFTD.Prelude
import AFTD.Kb.NumberTheory.DesignatedPartitionKTuple
import AFTD.Kb.NumberTheory.DesignatedPartitionSixTupleTenMod243
import AFTD.Kb.NumberTheory.DesignatedPartitionGenFun

/-!
# designated_partition_six_tuple_twenty_two_not_mod_729

Topic: elementary_number_theory   Node: 73e08d28f00a

Provenance: formalization of a published result. Source: arXiv:2611.05623 Conjecture 6.3

The number of designated partition 6-tuples of size 22, designated_partition_k_tuple 6 22, is not divisible by 729.
-/

noncomputable abbrev designated_partition_six_tuple_twenty_two_not_mod_729_fac :
    ℕ → PowerSeries ℕ := designated_partition_six_tuple_ten_mod_243_fac
private abbrev designated_partition_six_tuple_twenty_two_not_mod_729_facval :
    ℕ → ℕ → ℕ := designated_partition_six_tuple_ten_mod_243_facval

private def designated_partition_six_tuple_twenty_two_not_mod_729_one (M : ℕ) : List ℕ :=
  (List.range (M + 1)).map fun k => if k = 0 then 1 else 0

private def designated_partition_six_tuple_twenty_two_not_mod_729_facList (M i : ℕ) : List ℕ :=
  (List.range (M + 1)).map fun k => designated_partition_six_tuple_twenty_two_not_mod_729_facval i k

private def designated_partition_six_tuple_twenty_two_not_mod_729_mul (M : ℕ) (a b : List ℕ) : List ℕ :=
  (List.range (M + 1)).map fun n =>
    ∑ i ∈ Finset.range (n + 1), a.getD i 0 * b.getD (n - i) 0

private def designated_partition_six_tuple_twenty_two_not_mod_729_prodList (M : ℕ) : ℕ → List ℕ
  | 0 => designated_partition_six_tuple_twenty_two_not_mod_729_one M
  | (j + 1) =>
      designated_partition_six_tuple_twenty_two_not_mod_729_mul M
        (designated_partition_six_tuple_twenty_two_not_mod_729_prodList M j)
        (designated_partition_six_tuple_twenty_two_not_mod_729_facList M (j + 1))

private def designated_partition_six_tuple_twenty_two_not_mod_729_powList (M : ℕ) : ℕ → List ℕ
  | 0 => designated_partition_six_tuple_twenty_two_not_mod_729_one M
  | (m + 1) =>
      designated_partition_six_tuple_twenty_two_not_mod_729_mul M
        (designated_partition_six_tuple_twenty_two_not_mod_729_powList M m)
        (designated_partition_six_tuple_twenty_two_not_mod_729_prodList M M)

private def designated_partition_six_tuple_twenty_two_not_mod_729_rep
    (M : ℕ) (a : List ℕ) (φ : PowerSeries ℕ) : Prop :=
  ∀ k, k ≤ M → PowerSeries.coeff k φ = a.getD k 0

private lemma designated_partition_six_tuple_twenty_two_not_mod_729_getD_map_range
    (M k : ℕ) (f : ℕ → ℕ) (hk : k ≤ M) :
    ((List.range (M + 1)).map f).getD k 0 = f k := by
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  simp [List.getElem_map, List.getElem_range]

private lemma designated_partition_six_tuple_twenty_two_not_mod_729_rep_one (M : ℕ) :
    designated_partition_six_tuple_twenty_two_not_mod_729_rep M
      (designated_partition_six_tuple_twenty_two_not_mod_729_one M) (1 : PowerSeries ℕ) := by
  intro k hk
  rw [designated_partition_six_tuple_twenty_two_not_mod_729_one,
    designated_partition_six_tuple_twenty_two_not_mod_729_getD_map_range M k _ hk,
    PowerSeries.coeff_one]

private lemma designated_partition_six_tuple_twenty_two_not_mod_729_rep_facList
    (M i : ℕ) (hi : i ≠ 0) :
    designated_partition_six_tuple_twenty_two_not_mod_729_rep M
      (designated_partition_six_tuple_twenty_two_not_mod_729_facList M i)
      (designated_partition_six_tuple_twenty_two_not_mod_729_fac i) := by
  intro k hk
  rw [designated_partition_six_tuple_twenty_two_not_mod_729_facList,
    designated_partition_six_tuple_twenty_two_not_mod_729_getD_map_range M k _ hk]
  exact designated_partition_six_tuple_ten_mod_243_fac_coeff i hi k

private lemma designated_partition_six_tuple_twenty_two_not_mod_729_rep_mul
    (M : ℕ) {a b : List ℕ} {φ ψ : PowerSeries ℕ}
    (ha : designated_partition_six_tuple_twenty_two_not_mod_729_rep M a φ)
    (hb : designated_partition_six_tuple_twenty_two_not_mod_729_rep M b ψ) :
    designated_partition_six_tuple_twenty_two_not_mod_729_rep M
      (designated_partition_six_tuple_twenty_two_not_mod_729_mul M a b) (φ * ψ) := by
  intro k hk
  rw [designated_partition_six_tuple_twenty_two_not_mod_729_mul,
    designated_partition_six_tuple_ten_mod_243_coeff_mul_range,
    designated_partition_six_tuple_twenty_two_not_mod_729_getD_map_range M k _ hk]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have hi_le : i ≤ M := le_trans (Nat.le_of_lt_succ hi) hk
  have hki_le : k - i ≤ M := le_trans (Nat.sub_le _ _) hk
  rw [ha i hi_le, hb (k - i) hki_le]

private lemma designated_partition_six_tuple_twenty_two_not_mod_729_rep_prodList (M : ℕ) :
    ∀ j, designated_partition_six_tuple_twenty_two_not_mod_729_rep M
      (designated_partition_six_tuple_twenty_two_not_mod_729_prodList M j)
      (∏ i ∈ Finset.range j, designated_partition_six_tuple_twenty_two_not_mod_729_fac (i + 1))
  | 0 => by
      rw [designated_partition_six_tuple_twenty_two_not_mod_729_prodList,
        Finset.prod_range_zero]
      exact designated_partition_six_tuple_twenty_two_not_mod_729_rep_one M
  | (j + 1) => by
      rw [designated_partition_six_tuple_twenty_two_not_mod_729_prodList,
        Finset.prod_range_succ]
      exact designated_partition_six_tuple_twenty_two_not_mod_729_rep_mul M
        (designated_partition_six_tuple_twenty_two_not_mod_729_rep_prodList M j)
        (designated_partition_six_tuple_twenty_two_not_mod_729_rep_facList M (j + 1)
          (Nat.succ_ne_zero j))

private lemma designated_partition_six_tuple_twenty_two_not_mod_729_rep_powList (M : ℕ) :
    ∀ m, designated_partition_six_tuple_twenty_two_not_mod_729_rep M
      (designated_partition_six_tuple_twenty_two_not_mod_729_powList M m)
      ((∏ i ∈ Finset.range M, designated_partition_six_tuple_twenty_two_not_mod_729_fac (i + 1)) ^ m)
  | 0 => by
      rw [designated_partition_six_tuple_twenty_two_not_mod_729_powList, pow_zero]
      exact designated_partition_six_tuple_twenty_two_not_mod_729_rep_one M
  | (m + 1) => by
      rw [designated_partition_six_tuple_twenty_two_not_mod_729_powList, pow_succ]
      exact designated_partition_six_tuple_twenty_two_not_mod_729_rep_mul M
        (designated_partition_six_tuple_twenty_two_not_mod_729_rep_powList M m)
        (designated_partition_six_tuple_twenty_two_not_mod_729_rep_prodList M M)

private lemma designated_partition_six_tuple_twenty_two_not_mod_729_powList_value :
    (designated_partition_six_tuple_twenty_two_not_mod_729_powList 23 6).getD 22 0
      = 6635911068 := by decide

private lemma designated_partition_six_tuple_twenty_two_not_mod_729_coeff_F_eq
    (k : ℕ) (hk : k ≤ 22) :
    PowerSeries.coeff k designated_partition_gen_fun =
    PowerSeries.coeff k
      (∏ i ∈ Finset.range 23, designated_partition_six_tuple_twenty_two_not_mod_729_fac (i + 1)) := by
  rw [designated_partition_six_tuple_ten_mod_243_coeff_gen_fun k]
  exact (designated_partition_six_tuple_ten_mod_243_coeff_prod_range_stab k 23 (by omega) k le_rfl).symm

private lemma designated_partition_six_tuple_twenty_two_not_mod_729_coeff_F_pow_eq
    (m k : ℕ) (hk : k ≤ 22) :
    PowerSeries.coeff k (designated_partition_gen_fun ^ m) =
    PowerSeries.coeff k
      ((∏ i ∈ Finset.range 23, designated_partition_six_tuple_twenty_two_not_mod_729_fac (i + 1)) ^ m) := by
  induction m generalizing k with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, pow_succ,
        designated_partition_six_tuple_ten_mod_243_coeff_mul_range,
        designated_partition_six_tuple_ten_mod_243_coeff_mul_range]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      have hi_le : i ≤ 22 := by omega
      have hki_le : k - i ≤ 22 := by omega
      rw [ih i hi_le, designated_partition_six_tuple_twenty_two_not_mod_729_coeff_F_eq (k - i) hki_le]

private lemma designated_partition_six_tuple_twenty_two_not_mod_729_coeff_G_pow_val :
    PowerSeries.coeff 22
      ((∏ i ∈ Finset.range 23, designated_partition_six_tuple_twenty_two_not_mod_729_fac (i + 1)) ^ 6)
      = (designated_partition_six_tuple_twenty_two_not_mod_729_powList 23 6).getD 22 0 :=
  designated_partition_six_tuple_twenty_two_not_mod_729_rep_powList 23 6 22 (by norm_num)

/-- The number of designated partition 6-tuples of size 22 is not divisible by 729. -/
theorem designated_partition_six_tuple_twenty_two_not_mod_729 :
    ¬ (729 ∣ designated_partition_k_tuple 6 22) := by
  show ¬ (729 ∣ PowerSeries.coeff 22 (designated_partition_gen_fun ^ 6))
  rw [designated_partition_six_tuple_twenty_two_not_mod_729_coeff_F_pow_eq 6 22 (by norm_num),
    designated_partition_six_tuple_twenty_two_not_mod_729_coeff_G_pow_val,
    designated_partition_six_tuple_twenty_two_not_mod_729_powList_value]
  norm_num
