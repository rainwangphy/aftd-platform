import AFTD.Prelude
import AFTD.Kb.NumberTheory.DesignatedPartitionKTuple
import AFTD.Kb.NumberTheory.DesignatedPartitionGenFun
import AFTD.Kb.Tcs.F

/-!
# designated_partition_six_tuple_ten_mod_243

Topic: elementary_number_theory   Node: 91e0ed863584

Provenance: formalization of a published result. Source: arXiv:2611.05623 Conjecture 6.3

The number of designated partition 6-tuples of size 10, designated_partition_k_tuple 6 10, is divisible by 243.
-/

open PowerSeries
open scoped PowerSeries.WithPiTopology

/-- The generating-function factor attached to part size `i ≥ 1`. -/
noncomputable def designated_partition_six_tuple_ten_mod_243_fac (i : ℕ) : ℕ⟦X⟧ :=
  1 + ∑' j : ℕ, (j + 1 : ℕ) • X ^ (i * (j + 1))

/-- The `e`-th coefficient of the factor for part size `i` is `e / i` when `i ∣ e` and `e ≠ 0`. -/
lemma designated_partition_six_tuple_ten_mod_243_fac_coeff (i : ℕ) (hi : i ≠ 0) (e : ℕ) :
    (coeff e) (designated_partition_six_tuple_ten_mod_243_fac i)
      = if e = 0 then 1 else if i ∣ e then e / i else 0 := by
  have hsum : Summable (fun j : ℕ => (j + 1 : ℕ) • (X : ℕ⟦X⟧) ^ (i * (j + 1))) :=
    Nat.Partition.summable_genFun_term' (fun x c : ℕ => c) hi
  have hpush := hsum.map_tsum (coeff e) (WithPiTopology.continuous_coeff ℕ e)
  rw [designated_partition_six_tuple_ten_mod_243_fac, map_add, coeff_one, hpush]
  have hterm : (fun j : ℕ => (coeff e) ((j + 1 : ℕ) • (X : ℕ⟦X⟧) ^ (i * (j + 1))))
      = fun j : ℕ => if e = i * (j + 1) then (j + 1) else 0 := by
    funext j
    rw [map_smul, coeff_X_pow, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [hterm]
  rcases Nat.eq_zero_or_pos e with rfl | he
  · have hz : (fun j : ℕ => if 0 = i * (j + 1) then j + 1 else 0) = fun _ => 0 := by
      funext j
      have : i * (j + 1) ≠ 0 := (Nat.mul_pos (Nat.pos_of_ne_zero hi) (Nat.succ_pos j)).ne'
      rw [if_neg (Ne.symm this)]
    rw [hz, tsum_zero, add_zero]
    simp
  · have he0 : ¬ (e = 0) := by omega
    rw [if_neg he0, zero_add, if_neg he0]
    by_cases hd : i ∣ e
    · obtain ⟨c, hc⟩ := hd
      have hc0 : c ≠ 0 := by rintro rfl; rw [mul_zero] at hc; omega
      have hc1 : 1 ≤ c := Nat.one_le_iff_ne_zero.mpr hc0
      rw [if_pos ⟨c, hc⟩, tsum_eq_single (c - 1) ?_]
      · rw [Nat.sub_add_cancel hc1, if_pos hc, hc, Nat.mul_div_right c (Nat.pos_of_ne_zero hi)]
      · intro b hb
        rw [if_neg]
        intro hbe
        apply hb
        have h1 : i * (b + 1) = i * c := by rw [← hbe, hc]
        have hb1 : b + 1 = c := Nat.mul_left_cancel (Nat.pos_of_ne_zero hi) h1
        omega
    · rw [if_neg hd]
      have hz : (fun j : ℕ => if e = i * (j + 1) then j + 1 else 0) = fun _ => 0 := by
        funext j
        rw [if_neg]
        intro h
        exact hd ⟨j + 1, by rw [h, mul_comm]⟩
      rw [hz, tsum_zero]

/-- `F` is the product over `i` of the factors for part sizes `i+1`. -/
lemma designated_partition_six_tuple_ten_mod_243_fac_hasProd :
    HasProd (fun j : ℕ => designated_partition_six_tuple_ten_mod_243_fac (j + 1))
      designated_partition_gen_fun :=
  Nat.Partition.hasProd_genFun (fun _ c : ℕ => c) (R := ℕ)

/-- The antidiagonal of `n` is the image of `range (n+1)` under `i ↦ (i, n - i)`. -/
lemma designated_partition_six_tuple_ten_mod_243_antidiag_range (n : ℕ) :
    Finset.HasAntidiagonal.antidiagonal n
      = (Finset.range (n + 1)).image (fun i => (i, n - i)) := by
  ext p
  simp only [Finset.HasAntidiagonal.mem_antidiagonal, Finset.mem_image, Finset.mem_range]
  constructor
  · intro h
    exact ⟨p.1, by omega, Prod.ext rfl (by omega)⟩
  · rintro ⟨i, hi, h⟩
    rw [← h]
    omega

/-- Coefficient of a product as a convolution over `range (n+1)`. -/
lemma designated_partition_six_tuple_ten_mod_243_coeff_mul_range (φ ψ : ℕ⟦X⟧) (n : ℕ) :
    (coeff n) (φ * ψ) = ∑ i ∈ Finset.range (n + 1), (coeff i) φ * (coeff (n - i)) ψ := by
  rw [coeff_mul, designated_partition_six_tuple_ten_mod_243_antidiag_range, Finset.sum_image]
  simp

/-- The coefficient of a product is the convolution of the two explicit coefficient functions. -/
lemma designated_partition_six_tuple_ten_mod_243_coeff_mul_of_eq (φ ψ : ℕ⟦X⟧)
    (v w : ℕ → ℕ) (n : ℕ)
    (hφ : ∀ k ≤ n, (coeff k) φ = v k) (hψ : ∀ k ≤ n, (coeff k) ψ = w k) :
    (coeff n) (φ * ψ) = ∑ i ∈ Finset.range (n + 1), v i * w (n - i) := by
  rw [designated_partition_six_tuple_ten_mod_243_coeff_mul_range]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [hφ i (by simpa using hi), hψ (n - i) (Nat.sub_le n i)]

/-- Multiplying by a series with constant term one and vanishing low-degree terms fixes low-degree coefficients. -/
lemma designated_partition_six_tuple_ten_mod_243_coeff_mul_of_triv (φ ψ : ℕ⟦X⟧) (d : ℕ)
    (h0 : (coeff 0) ψ = 1) (hψ : ∀ k, 1 ≤ k → k ≤ d → (coeff k) ψ = 0) :
    ∀ k ≤ d, (coeff k) (φ * ψ) = (coeff k) φ := by
  intro k hk
  have hkk : (coeff (k - k)) ψ = (1 : ℕ) := by rw [Nat.sub_self]; exact h0
  have hsum : (∑ i ∈ Finset.range (k + 1), (coeff i) φ * (coeff (k - i)) ψ)
      = (coeff k) φ * (coeff (k - k)) ψ := by
    refine Finset.sum_eq_single (s := Finset.range (k + 1))
      (f := fun i => (coeff i) φ * (coeff (n := k - i) ψ)) k ?_ ?_
    · intro b hb hbk
      have hb' : b ≤ k := by simpa using hb
      have hpos : 1 ≤ k - b := by omega
      rw [hψ (k - b) hpos (by omega), mul_zero]
    · intro hk'
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self k)) hk'
  rw [designated_partition_six_tuple_ten_mod_243_coeff_mul_range, hsum, hkk, mul_one]

/-- Coefficients of degree at most `d` of a truncated product stabilize once all factors of index `≤ d+1` are present. -/
lemma designated_partition_six_tuple_ten_mod_243_coeff_prod_range_stab (d : ℕ) :
    ∀ b, d + 1 ≤ b → ∀ k ≤ d,
      (coeff k) (∏ i ∈ Finset.range b, designated_partition_six_tuple_ten_mod_243_fac (i + 1))
        = (coeff k)
          (∏ i ∈ Finset.range (d + 1), designated_partition_six_tuple_ten_mod_243_fac (i + 1)) := by
  intro b hb
  induction b, hb using Nat.le_induction with
  | base => intro k hk; rfl
  | succ b hb ih =>
      intro k hk
      rw [Finset.prod_range_succ]
      rw [designated_partition_six_tuple_ten_mod_243_coeff_mul_of_triv _ _ d ?_ ?_ k hk, ih k hk]
      · rw [designated_partition_six_tuple_ten_mod_243_fac_coeff (b + 1) (by omega) 0]; simp
      · intro j hj1 hjd
        rw [designated_partition_six_tuple_ten_mod_243_fac_coeff (b + 1) (by omega) j,
          if_neg (by omega : ¬ j = 0), if_neg]
        intro hdvd
        have := Nat.le_of_dvd (by omega : 0 < j) hdvd
        omega

/-- The `d`-th coefficient of `F` equals the `d`-th coefficient of the first `d+1` factors. -/
lemma designated_partition_six_tuple_ten_mod_243_coeff_gen_fun (d : ℕ) :
    (coeff d) designated_partition_gen_fun
      = (coeff d)
          (∏ i ∈ Finset.range (d + 1), designated_partition_six_tuple_ten_mod_243_fac (i + 1)) := by
  have hc := (WithPiTopology.tendsto_iff_coeff_tendsto ℕ _ Filter.atTop
    designated_partition_gen_fun).mp
    designated_partition_six_tuple_ten_mod_243_fac_hasProd.tendsto_prod_nat d
  have hev : ∀ᶠ b in Filter.atTop,
      (coeff d) (∏ i ∈ Finset.range b, designated_partition_six_tuple_ten_mod_243_fac (i + 1))
        = (coeff d) designated_partition_gen_fun :=
    hc.eventually ((isOpen_discrete ({coeff d designated_partition_gen_fun} : Set ℕ)).mem_nhds rfl)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  rw [← hN (max N (d + 1)) (le_max_left _ _)]
  exact designated_partition_six_tuple_ten_mod_243_coeff_prod_range_stab d (max N (d+1))
    (le_max_right _ _) d le_rfl

/-- The explicit (computable) coefficient function of a single factor. -/
def designated_partition_six_tuple_ten_mod_243_facval (i e : ℕ) : ℕ :=
  if e = 0 then 1 else if i ∣ e then e / i else 0

/-- Truncated convolution of two coefficient functions. -/
def designated_partition_six_tuple_ten_mod_243_conv (a b : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), a i * b (n - i)

/-- Coefficients of the product of the factors `1, …, j`, computed by iterated convolution. -/
def designated_partition_six_tuple_ten_mod_243_pv : ℕ → ℕ → ℕ
  | 0, n => if n = 0 then 1 else 0
  | (j + 1), n => designated_partition_six_tuple_ten_mod_243_conv
      (designated_partition_six_tuple_ten_mod_243_pv j)
      (designated_partition_six_tuple_ten_mod_243_facval (j + 1)) n

/-- Coefficients of the `m`-th power of the product of the first eleven factors, by iterated convolution. -/
def designated_partition_six_tuple_ten_mod_243_powv : ℕ → ℕ → ℕ
  | 0, n => if n = 0 then 1 else 0
  | (m + 1), n => designated_partition_six_tuple_ten_mod_243_conv
      (designated_partition_six_tuple_ten_mod_243_powv m)
      (designated_partition_six_tuple_ten_mod_243_pv 11) n

/-- `pv j k` is the `k`-th coefficient of the product of the first `j` factors, for `k ≤ 10`. -/
lemma designated_partition_six_tuple_ten_mod_243_pv_spec (j : ℕ) :
    ∀ k ≤ 10, (coeff k) (∏ i ∈ Finset.range j, designated_partition_six_tuple_ten_mod_243_fac (i + 1))
      = designated_partition_six_tuple_ten_mod_243_pv j k := by
  induction j with
  | zero => intro k hk; simp [designated_partition_six_tuple_ten_mod_243_pv]
  | succ j ih =>
      intro k hk
      rw [Finset.prod_range_succ]
      rw [designated_partition_six_tuple_ten_mod_243_coeff_mul_of_eq _ _
        (designated_partition_six_tuple_ten_mod_243_pv j)
        (designated_partition_six_tuple_ten_mod_243_facval (j + 1)) k
        (fun e he => ih e (le_trans he hk)) ?_]
      · rfl
      · intro e he
        simpa [designated_partition_six_tuple_ten_mod_243_facval] using
          designated_partition_six_tuple_ten_mod_243_fac_coeff (j + 1) (Nat.succ_ne_zero j) e

/-- The first eleven coefficients of `F` are given by `pv 11`. -/
lemma designated_partition_six_tuple_ten_mod_243_gen_fun_coeff (k : ℕ) (hk : k ≤ 10) :
    (coeff k) designated_partition_gen_fun
      = designated_partition_six_tuple_ten_mod_243_pv 11 k := by
  rw [designated_partition_six_tuple_ten_mod_243_coeff_gen_fun k]
  rw [← designated_partition_six_tuple_ten_mod_243_coeff_prod_range_stab k 11 (by omega) k le_rfl]
  exact designated_partition_six_tuple_ten_mod_243_pv_spec 11 k hk

/-- `powv m k` is the `k`-th coefficient of the `m`-th power of the product of the first eleven factors. -/
lemma designated_partition_six_tuple_ten_mod_243_powv_spec (m : ℕ) :
    ∀ k ≤ 10,
      (coeff k)
        ((∏ i ∈ Finset.range 11, designated_partition_six_tuple_ten_mod_243_fac (i + 1)) ^ m)
        = designated_partition_six_tuple_ten_mod_243_powv m k := by
  induction m with
  | zero => intro k hk; simp [designated_partition_six_tuple_ten_mod_243_powv]
  | succ m ih =>
      intro k hk
      rw [pow_succ, designated_partition_six_tuple_ten_mod_243_coeff_mul_of_eq _ _
        (designated_partition_six_tuple_ten_mod_243_powv m)
        (designated_partition_six_tuple_ten_mod_243_pv 11) k
        (fun e he => ih e (le_trans he hk))
        (fun e he => designated_partition_six_tuple_ten_mod_243_pv_spec 11 e (le_trans he hk))]
      rfl

/-- Coefficients of degree at most 10 of `F^m` only depend on the coefficients of `F` of degree at most 10. -/
lemma designated_partition_six_tuple_ten_mod_243_pow_congr (m : ℕ) :
    ∀ k ≤ 10, (coeff k) (designated_partition_gen_fun ^ m)
      = (coeff k)
          ((∏ i ∈ Finset.range 11, designated_partition_six_tuple_ten_mod_243_fac (i + 1)) ^ m) := by
  induction m with
  | zero => intro k hk; simp
  | succ m ih =>
      intro k hk
      rw [pow_succ, pow_succ, designated_partition_six_tuple_ten_mod_243_coeff_mul_range,
        designated_partition_six_tuple_ten_mod_243_coeff_mul_range]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ k := by simpa using hi
      rw [ih i (le_trans hi' hk),
        designated_partition_six_tuple_ten_mod_243_gen_fun_coeff (k - i) (by omega),
        designated_partition_six_tuple_ten_mod_243_pv_spec 11 (k - i) (by omega)]

/-- The computable value of the tenth coefficient of the sixth power of `F`. -/
lemma designated_partition_six_tuple_ten_mod_243_powv_value :
    designated_partition_six_tuple_ten_mod_243_powv 6 10 = 384183 := by decide

/-- The number of designated partition 6-tuples of size 10 is divisible by 243. -/
theorem designated_partition_six_tuple_ten_mod_243 :
    243 ∣ designated_partition_k_tuple 6 10 := by
  have h : designated_partition_k_tuple 6 10
      = designated_partition_six_tuple_ten_mod_243_powv 6 10 := by
    show (coeff 10) (designated_partition_gen_fun ^ 6)
      = designated_partition_six_tuple_ten_mod_243_powv 6 10
    rw [designated_partition_six_tuple_ten_mod_243_pow_congr 6 10 le_rfl,
      designated_partition_six_tuple_ten_mod_243_powv_spec 6 10 le_rfl]
  rw [h, designated_partition_six_tuple_ten_mod_243_powv_value]
  norm_num
