import AFTD.Prelude
import AFTD.Kb.NumberTheory.DesignatedPartitionKTuple
import AFTD.Kb.NumberTheory.DesignatedPartitionSixTupleTwentyTwoNotMod729
import AFTD.Kb.NumberTheory.DesignatedPartitionGenFun
import AFTD.Kb.NumberTheory.DesignatedPartitionSixTupleTenMod243
import AFTD.Kb.Tcs.F

/-!
# designated_partition_six_tuple_twenty_two_divisible_by_243

Topic: elementary_number_theory   Node: 0c99fa268d41

Provenance: helper lemma. arXiv:2611.05623 Conjecture 6.3

The number of designated partition 6-tuples of size 22, designated_partition_k_tuple 6 22, is divisible by 243.
-/

open Finset PowerSeries

/-- Explicit value of the coefficient of `fac i` at degree `e`. -/
def designated_partition_six_tuple_twenty_two_divisible_by_243_facVal (i e : ℕ) : ℕ :=
  if e = 0 then 1 else if i ∣ e then e / i else 0

/-- The first `L` coefficients of `fac i`, as a list. -/
def designated_partition_six_tuple_twenty_two_divisible_by_243_facList (i L : ℕ) : List ℕ :=
  (List.range L).map (designated_partition_six_tuple_twenty_two_divisible_by_243_facVal i)

/-- The first `L` coefficients of the constant power series 1. -/
def designated_partition_six_tuple_twenty_two_divisible_by_243_oneList (L : ℕ) : List ℕ :=
  (List.range L).map (fun k => if k = 0 then 1 else 0)

/-- Truncated convolution of two coefficient lists up to degree `L-1`. -/
def designated_partition_six_tuple_twenty_two_divisible_by_243_conv (L : ℕ) (a b : List ℕ) : List ℕ :=
  (List.range L).map fun k => ∑ i ∈ Finset.range (k+1), a.getD i 0 * b.getD (k - i) 0

/-- Coefficients of the partial products `∏ (i+1) ≤ j, fac (i+1)`. -/
def designated_partition_six_tuple_twenty_two_divisible_by_243_pvList : ℕ → ℕ → List ℕ
  | 0, L => designated_partition_six_tuple_twenty_two_divisible_by_243_oneList L
  | j+1, L => designated_partition_six_tuple_twenty_two_divisible_by_243_conv L
      (designated_partition_six_tuple_twenty_two_divisible_by_243_pvList j L)
      (designated_partition_six_tuple_twenty_two_divisible_by_243_facList (j+1) L)

/-- Coefficients of the `m`-th power of the truncated product of the first `M` factors. -/
def designated_partition_six_tuple_twenty_two_divisible_by_243_pwList (M : ℕ) : ℕ → ℕ → List ℕ
  | 0, L => designated_partition_six_tuple_twenty_two_divisible_by_243_oneList L
  | m+1, L => designated_partition_six_tuple_twenty_two_divisible_by_243_conv L
      (designated_partition_six_tuple_twenty_two_divisible_by_243_pwList M m L)
      (designated_partition_six_tuple_twenty_two_divisible_by_243_pvList M L)

/-- Reading the `k`-th entry below `L` from a mapped `List.range`. -/
lemma designated_partition_six_tuple_twenty_two_divisible_by_243_list_getD_map_range
    (f : ℕ → ℕ) (L k : ℕ) (hk : k < L) :
    ((List.range L).map f).getD k 0 = f k := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  rfl

/-- The one list represents the coefficients of `1`. -/
lemma designated_partition_six_tuple_twenty_two_divisible_by_243_oneList_spec
    (L k : ℕ) (hk : k < L) :
    (designated_partition_six_tuple_twenty_two_divisible_by_243_oneList L).getD k 0 =
      PowerSeries.coeff k (1 : PowerSeries ℕ) := by
  simp only [designated_partition_six_tuple_twenty_two_divisible_by_243_oneList,
    designated_partition_six_tuple_twenty_two_divisible_by_243_list_getD_map_range _ L k hk]
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · subst hk0; simp
  · rw [if_neg (by omega)]
    exact (PowerSeries.coeff_one (R := ℕ) k).trans (if_neg (by omega)) |>.symm

/-- The fac list gives the explicit factor coefficients. -/
lemma designated_partition_six_tuple_twenty_two_divisible_by_243_facList_getD
    (i L k : ℕ) (hk : k < L) :
    (designated_partition_six_tuple_twenty_two_divisible_by_243_facList i L).getD k 0 =
      designated_partition_six_tuple_twenty_two_divisible_by_243_facVal i k :=
  designated_partition_six_tuple_twenty_two_divisible_by_243_list_getD_map_range
    (designated_partition_six_tuple_twenty_two_divisible_by_243_facVal i) L k hk

/-- `facVal i e` is the coefficient of `fac i` at degree `e`. -/
lemma designated_partition_six_tuple_twenty_two_divisible_by_243_facVal_coeff
    (i : ℕ) (hi : i ≠ 0) (e : ℕ) :
    (PowerSeries.coeff e) (designated_partition_six_tuple_ten_mod_243_fac i) =
      designated_partition_six_tuple_twenty_two_divisible_by_243_facVal i e :=
  designated_partition_six_tuple_ten_mod_243_fac_coeff i hi e

/-- The convolution list computes the coefficient of the product. -/
lemma designated_partition_six_tuple_twenty_two_divisible_by_243_conv_spec
    (L : ℕ) (a b : List ℕ) (φ ψ : PowerSeries ℕ)
    (ha : ∀ k, k < L → a.getD k 0 = PowerSeries.coeff k φ)
    (hb : ∀ k, k < L → b.getD k 0 = PowerSeries.coeff k ψ) :
    ∀ k, k < L →
      (designated_partition_six_tuple_twenty_two_divisible_by_243_conv L a b).getD k 0 =
        PowerSeries.coeff k (φ * ψ) := by
  intro k hk
  rw [designated_partition_six_tuple_twenty_two_divisible_by_243_conv,
    designated_partition_six_tuple_twenty_two_divisible_by_243_list_getD_map_range _ L k hk,
    designated_partition_six_tuple_ten_mod_243_coeff_mul_range]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [ha i (by omega), hb (k - i) (by omega)]

/-- The partial-product list computes the coefficients of the partial products. -/
lemma designated_partition_six_tuple_twenty_two_divisible_by_243_pvList_spec (j : ℕ) :
    ∀ L k, k < L →
      (designated_partition_six_tuple_twenty_two_divisible_by_243_pvList j L).getD k 0 =
        PowerSeries.coeff k (∏ i ∈ Finset.range j,
          designated_partition_six_tuple_ten_mod_243_fac (i + 1)) := by
  induction j with
  | zero =>
    intro L k hk
    simp only [designated_partition_six_tuple_twenty_two_divisible_by_243_pvList,
      Finset.range_zero, Finset.prod_empty]
    exact designated_partition_six_tuple_twenty_two_divisible_by_243_oneList_spec L k hk
  | succ j ih =>
    intro L k hk
    simp only [designated_partition_six_tuple_twenty_two_divisible_by_243_pvList]
    rw [designated_partition_six_tuple_twenty_two_divisible_by_243_conv_spec L _ _ _ _
      (fun i hi => ih L i hi)
      (fun i hi =>
        (designated_partition_six_tuple_twenty_two_divisible_by_243_facList_getD (j+1) L i hi).trans
          (designated_partition_six_tuple_twenty_two_divisible_by_243_facVal_coeff (j+1) (by omega) i).symm)
      k hk]
    rw [Finset.prod_range_succ]

/-- The power list computes the coefficients of the `m`-th power of the truncation. -/
lemma designated_partition_six_tuple_twenty_two_divisible_by_243_pwList_spec (M m : ℕ) :
    ∀ L k, k < L →
      (designated_partition_six_tuple_twenty_two_divisible_by_243_pwList M m L).getD k 0 =
        PowerSeries.coeff k ((∏ i ∈ Finset.range M,
          designated_partition_six_tuple_ten_mod_243_fac (i + 1)) ^ m) := by
  induction m with
  | zero =>
    intro L k hk
    simp only [designated_partition_six_tuple_twenty_two_divisible_by_243_pwList, pow_zero]
    exact designated_partition_six_tuple_twenty_two_divisible_by_243_oneList_spec L k hk
  | succ m ih =>
    intro L k hk
    simp only [designated_partition_six_tuple_twenty_two_divisible_by_243_pwList]
    rw [designated_partition_six_tuple_twenty_two_divisible_by_243_conv_spec L _ _ _ _
      (fun i hi => ih L i hi)
      (fun i hi => designated_partition_six_tuple_twenty_two_divisible_by_243_pvList_spec M L i hi)
      k hk]
    rw [pow_succ]

/-- Below degree 22, `F` agrees with the product of the first 22 factors. -/
lemma designated_partition_six_tuple_twenty_two_divisible_by_243_coeff_gen_fun_eq
    (k : ℕ) (hk : k ≤ 22) :
    PowerSeries.coeff k designated_partition_gen_fun =
      PowerSeries.coeff k (∏ i ∈ Finset.range 23,
        designated_partition_six_tuple_ten_mod_243_fac (i + 1)) := by
  rw [designated_partition_six_tuple_ten_mod_243_coeff_gen_fun k,
    (designated_partition_six_tuple_ten_mod_243_coeff_prod_range_stab k 23 (by omega) k (le_rfl)).symm]

/-- Below degree 22, all powers of `F` agree with those of the truncation. -/
lemma designated_partition_six_tuple_twenty_two_divisible_by_243_pow_coeff_eq (m : ℕ) :
    ∀ k ≤ 22,
      PowerSeries.coeff k (designated_partition_gen_fun ^ m) =
        PowerSeries.coeff k ((∏ i ∈ Finset.range 23,
          designated_partition_six_tuple_ten_mod_243_fac (i + 1)) ^ m) := by
  induction m with
  | zero => intro k hk; simp
  | succ m ih =>
    intro k hk
    rw [pow_succ, pow_succ,
      designated_partition_six_tuple_ten_mod_243_coeff_mul_range,
      designated_partition_six_tuple_ten_mod_243_coeff_mul_range]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [ih i (by omega), designated_partition_six_tuple_twenty_two_divisible_by_243_coeff_gen_fun_eq (k - i) (by omega)]

/-- The number of designated partition 6-tuples of size 22 is divisible by 243. -/
theorem designated_partition_six_tuple_twenty_two_divisible_by_243 :
    243 ∣ designated_partition_k_tuple 6 22 := by
  show 243 ∣ PowerSeries.coeff 22 (designated_partition_gen_fun ^ 6)
  rw [designated_partition_six_tuple_twenty_two_divisible_by_243_pow_coeff_eq 6 22 (by norm_num)]
  rw [← designated_partition_six_tuple_twenty_two_divisible_by_243_pwList_spec 23 6 23 22 (by norm_num)]
  have hval : (designated_partition_six_tuple_twenty_two_divisible_by_243_pwList 23 6 23).getD 22 0 = 6635911068 := by decide
  rw [hval]
  norm_num
