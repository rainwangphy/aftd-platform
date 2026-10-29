import AFTD.Prelude
import AFTD.Kb.Tcs.GenKServerUniformIsRandAlg
import AFTD.Kb.Tcs.GenKServerUniformExpectedCost
import AFTD.Kb.Tcs.GenKServerUniformOpt
import AFTD.Kb.Tcs.GenKServerUniformExpectedCostFrom
import AFTD.Kb.Tcs.GenKServerUniformPathCost
import AFTD.Kb.Tcs.Weight

/-!
# gen_k_server_uniform_log_competitive

Topic: online_algorithms   Node: bbbd25c47110

Provenance: formalization of a published result. Source: arXiv:2610.37192, Theorem 1.1, specialized to k spaces with m points each (the paper allows any uniform spaces, finite or infinite)

For every k ≥ 1, every m and every start configuration a : Fin k → Fin m of generalized k-server on k uniform metrics with m points each (unit distances), there are transition probabilities P with gen_k_server_uniform_is_rand_alg P such that for every finite request list ρ, the expected cost gen_k_server_uniform_expected_cost P a ρ is at most (k + 1) · ln(2k) · gen_k_server_uniform_opt a ρ, with no additive constant.
-/

/-- Sub-stochastic kernel of the weight update: a configuration serving `r` keeps its weight,
one failing `r` passes `1/(2k)` of it to each of its `k` repairs. -/
noncomputable def gen_k_server_log_K {k m : ℕ} (r x y : Fin k → Fin m) : ℝ :=
  if ∃ i, x i = r i then (if y = x then 1 else 0)
  else ((2 * k : ℝ))⁻¹ * ∑ i, if y = Function.update x i (r i) then 1 else 0

/-- One weight update at request `r`. -/
noncomputable def gen_k_server_log_T {k m : ℕ} (r : Fin k → Fin m) (φ : (Fin k → Fin m) → ℝ)
    (y : Fin k → Fin m) : ℝ :=
  ∑ x, φ x * gen_k_server_log_K r x y

/-- The weights after the requests `past`, starting from the point mass at `a`. -/
noncomputable def gen_k_server_log_W {k m : ℕ} (a : Fin k → Fin m) (past : List (Fin k → Fin m)) :
    (Fin k → Fin m) → ℝ :=
  past.foldl (fun φ r => gen_k_server_log_T r φ) (fun x => if x = a then 1 else 0)

/-- The algorithm: stay when serving; otherwise with probability 1/2 a uniform repair,
with probability 1/2 a fresh sample from the normalized new weights. -/
noncomputable def gen_k_server_log_P {k m : ℕ} (a : Fin k → Fin m) (past : List (Fin k → Fin m))
    (r x y : Fin k → Fin m) : ℝ :=
  gen_k_server_log_K r x y + (if ∃ i, x i = r i then 0 else 1 / 2) *
    (gen_k_server_log_W a (past ++ [r]) y / ∑ z, gen_k_server_log_W a (past ++ [r]) z)

lemma gen_k_server_log_K_nonneg {k m : ℕ} (r x y : Fin k → Fin m) : 0 ≤ gen_k_server_log_K r x y := by
  unfold gen_k_server_log_K
  split_ifs
  · norm_num
  · norm_num
  · apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg fun i _ => by split_ifs <;> norm_num

lemma gen_k_server_log_K_sum {k m : ℕ} (hk : 1 ≤ k) (r x : Fin k → Fin m) :
    ∑ y, gen_k_server_log_K r x y = if ∃ i, x i = r i then 1 else 1 / 2 := by
  open Finset in
  unfold gen_k_server_log_K
  split_ifs with h
  · simp
  · rw [← mul_sum, sum_comm]
    simp only [sum_ite_eq', mem_univ, if_true, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    have : (k : ℝ) ≠ 0 := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    field_simp

lemma gen_k_server_log_K_serves {k m : ℕ} (r x y : Fin k → Fin m) (h : gen_k_server_log_K r x y ≠ 0) :
    ∃ i, y i = r i := by
  open Finset in
  unfold gen_k_server_log_K at h
  split_ifs at h with hx hy
  · subst hy; exact hx
  · exact absurd rfl h
  · by_contra hn
    push Not at hn
    apply h
    rw [sum_eq_zero, mul_zero]
    intro i _
    rw [if_neg]
    intro he
    apply hn i
    rw [he, Function.update_self]

lemma gen_k_server_log_hd_update_le {k m : ℕ} (x : Fin k → Fin m) (i : Fin k) (v : Fin m) :
    hammingDist x (Function.update x i v) ≤ 1 := by
  open Finset in
  unfold hammingDist
  calc _ ≤ ({i} : Finset (Fin k)).card := by
        apply card_le_card
        intro j hj
        simp only [mem_filter, mem_univ, true_and] at hj
        by_contra hne
        rw [mem_singleton] at hne
        exact hj (by rw [Function.update_of_ne hne])
    _ = 1 := card_singleton i

lemma gen_k_server_log_hd_update_succ {k m : ℕ} (u o : Fin k → Fin m) (i : Fin k) (h : u i ≠ o i) :
    hammingDist (Function.update u i (o i)) o + 1 = hammingDist u o := by
  open Finset in
  unfold hammingDist
  have : (univ.filter fun j => Function.update u i (o i) j ≠ o j) =
      (univ.filter fun j => u j ≠ o j).erase i := by
    ext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  rw [this, card_erase_add_one]
  simp [h]

lemma gen_k_server_log_K_cost {k m : ℕ} (hk : 1 ≤ k) (r x : Fin k → Fin m) :
    ∑ y, gen_k_server_log_K r x y * (hammingDist x y : ℝ) ≤ if ∃ i, x i = r i then 0 else 1 / 2 := by
  open Finset in
  unfold gen_k_server_log_K
  split_ifs with h
  · simp
  · simp_rw [mul_assoc, ← mul_sum, sum_mul]
    rw [sum_comm]
    simp only [ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, if_true]
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
    have hle : ∑ i : Fin k, (hammingDist x (Function.update x i (r i)) : ℝ) ≤ k := by
      calc _ ≤ ∑ _i : Fin k, (1 : ℝ) := sum_le_sum fun i _ => by
              exact_mod_cast gen_k_server_log_hd_update_le x i (r i)
        _ = k := by simp
    rw [inv_mul_le_iff₀ (by positivity)]
    linarith

lemma gen_k_server_log_T_nonneg {k m : ℕ} (r : Fin k → Fin m) (φ : (Fin k → Fin m) → ℝ)
    (hφ : ∀ x, 0 ≤ φ x) (y : Fin k → Fin m) : 0 ≤ gen_k_server_log_T r φ y :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hφ x) (gen_k_server_log_K_nonneg r x y)

lemma gen_k_server_log_T_sum {k m : ℕ} (hk : 1 ≤ k) (r : Fin k → Fin m) (φ : (Fin k → Fin m) → ℝ) :
    ∑ y, gen_k_server_log_T r φ y = ∑ x, φ x * (if ∃ i, x i = r i then 1 else 1 / 2) := by
  open Finset in
  unfold gen_k_server_log_T
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [← mul_sum, gen_k_server_log_K_sum hk]

lemma gen_k_server_log_T_ge {k m : ℕ} (r : Fin k → Fin m) (φ : (Fin k → Fin m) → ℝ)
    (hφ : ∀ x, 0 ≤ φ x) (x y : Fin k → Fin m) : φ x * gen_k_server_log_K r x y ≤ gen_k_server_log_T r φ y :=
  Finset.single_le_sum (f := fun x => φ x * gen_k_server_log_K r x y)
    (fun x _ => mul_nonneg (hφ x) (gen_k_server_log_K_nonneg r x y)) (Finset.mem_univ x)

lemma gen_k_server_log_W_append {k m : ℕ} (a : Fin k → Fin m) (past : List (Fin k → Fin m))
    (r : Fin k → Fin m) : gen_k_server_log_W a (past ++ [r]) = gen_k_server_log_T r (gen_k_server_log_W a past) := by
  simp [gen_k_server_log_W, List.foldl_append]

lemma gen_k_server_log_foldl_pos {k m : ℕ} (hk : 1 ≤ k) (past : List (Fin k → Fin m)) :
    ∀ φ : (Fin k → Fin m) → ℝ, (∀ x, 0 ≤ φ x) → 0 < ∑ x, φ x →
      (∀ x, 0 ≤ past.foldl (fun φ r => gen_k_server_log_T r φ) φ x) ∧
        0 < ∑ x, past.foldl (fun φ r => gen_k_server_log_T r φ) φ x := by
  open Finset in
  induction past with
  | nil => intro φ h1 h2; exact ⟨h1, h2⟩
  | cons r rs ih =>
    intro φ h1 h2
    apply ih
    · exact gen_k_server_log_T_nonneg r φ h1
    · rw [gen_k_server_log_T_sum hk]
      calc 0 < ∑ x, φ x * (1 / 2) := by rw [← sum_mul]; positivity
        _ ≤ _ := sum_le_sum fun x _ => by
            apply mul_le_mul_of_nonneg_left _ (h1 x)
            split_ifs <;> norm_num

lemma gen_k_server_log_W_nonneg {k m : ℕ} (hk : 1 ≤ k) (a : Fin k → Fin m) (past : List (Fin k → Fin m))
    (x : Fin k → Fin m) : 0 ≤ gen_k_server_log_W a past x :=
  (gen_k_server_log_foldl_pos hk past _ (fun x => by split_ifs <;> norm_num)
    (by simp)).1 x

lemma gen_k_server_log_W_sum_pos {k m : ℕ} (hk : 1 ≤ k) (a : Fin k → Fin m) (past : List (Fin k → Fin m)) :
    0 < ∑ x, gen_k_server_log_W a past x :=
  (gen_k_server_log_foldl_pos hk past _ (fun x => by split_ifs <;> norm_num) (by simp)).2

lemma gen_k_server_log_is_rand_alg {k m : ℕ} (hk : 1 ≤ k) (a : Fin k → Fin m) :
    gen_k_server_uniform_is_rand_alg (gen_k_server_log_P a) := by
  open Finset in
  intro past r x
  have hpos := gen_k_server_log_W_sum_pos hk a (past ++ [r])
  refine ⟨fun y => ?_, ?_, fun y hy => ?_⟩
  · unfold gen_k_server_log_P
    have := gen_k_server_log_K_nonneg r x y
    have := gen_k_server_log_W_nonneg hk a (past ++ [r]) y
    have : 0 ≤ (if ∃ i, x i = r i then (0 : ℝ) else 1 / 2) := by split_ifs <;> norm_num
    positivity
  · unfold gen_k_server_log_P
    rw [sum_add_distrib, gen_k_server_log_K_sum hk, ← mul_sum, ← sum_div, div_self hpos.ne']
    split_ifs <;> norm_num
  · unfold gen_k_server_log_P at hy
    by_cases hK : gen_k_server_log_K r x y = 0
    · rw [hK, zero_add] at hy
      have hW : gen_k_server_log_W a (past ++ [r]) y ≠ 0 := by
        intro h0; apply hy; rw [h0, zero_div, mul_zero]
      rw [gen_k_server_log_W_append] at hW
      unfold gen_k_server_log_T at hW
      obtain ⟨x', _, hx'⟩ := exists_ne_zero_of_sum_ne_zero hW
      exact gen_k_server_log_K_serves r x' y (right_ne_zero_of_mul hx')
    · exact gen_k_server_log_K_serves r x y hK

/-- The configuration stays distributed as the normalized weights. -/
lemma gen_k_server_log_dist {k m : ℕ} (hk : 1 ≤ k) (a : Fin k → Fin m) (past : List (Fin k → Fin m))
    (r y : Fin k → Fin m) :
    ∑ x, gen_k_server_log_W a past x / (∑ z, gen_k_server_log_W a past z) * gen_k_server_log_P a past r x y =
      gen_k_server_log_W a (past ++ [r]) y / ∑ z, gen_k_server_log_W a (past ++ [r]) z := by
  open Finset in
  have hΦ := gen_k_server_log_W_sum_pos hk a past
  have hΦ' := gen_k_server_log_W_sum_pos hk a (past ++ [r])
  set φ := gen_k_server_log_W a past
  set Φ := ∑ z, φ z
  set Φ' := ∑ z, gen_k_server_log_W a (past ++ [r]) z with hΦ'def
  set q := gen_k_server_log_W a (past ++ [r]) y / Φ'
  have hsplit : ∑ x, φ x / Φ * gen_k_server_log_P a past r x y =
      (∑ x, φ x * gen_k_server_log_K r x y) / Φ +
        (∑ x, φ x * (if ∃ i, x i = r i then 0 else 1 / 2)) / Φ * q := by
    rw [sum_div, sum_div, sum_mul, ← sum_add_distrib]
    refine sum_congr rfl fun x _ => ?_
    unfold gen_k_server_log_P
    ring
  have hy : ∑ x, φ x * gen_k_server_log_K r x y = gen_k_server_log_W a (past ++ [r]) y := by
    rw [gen_k_server_log_W_append]; rfl
  have hsum : Φ' + ∑ x, φ x * (if ∃ i, x i = r i then (0 : ℝ) else 1 / 2) = Φ := by
    rw [hΦ'def, gen_k_server_log_W_append, gen_k_server_log_T_sum hk, ← sum_add_distrib]
    refine sum_congr rfl fun x _ => ?_
    split_ifs <;> ring
  rw [hsplit, hy]
  simp only [q]
  field_simp
  linear_combination (gen_k_server_log_W a (past ++ [r]) y) * hsum

/-- Expected movement at one step is at most `(k+1)(1 - Φ'/Φ)`. -/
lemma gen_k_server_log_cost {k m : ℕ} (hk : 1 ≤ k) (a : Fin k → Fin m) (past : List (Fin k → Fin m))
    (r : Fin k → Fin m) :
    ∑ x, ∑ y, gen_k_server_log_W a past x / (∑ z, gen_k_server_log_W a past z) * gen_k_server_log_P a past r x y *
        (hammingDist x y : ℝ) ≤
      ((k : ℝ) + 1) * (1 - (∑ z, gen_k_server_log_W a (past ++ [r]) z) / ∑ z, gen_k_server_log_W a past z) := by
  open Finset in
  have hΦ := gen_k_server_log_W_sum_pos hk a past
  have hΦ' := gen_k_server_log_W_sum_pos hk a (past ++ [r])
  have hsum : ∑ z, gen_k_server_log_W a (past ++ [r]) z +
      ∑ x, gen_k_server_log_W a past x * (if ∃ i, x i = r i then (0 : ℝ) else 1 / 2) =
        ∑ z, gen_k_server_log_W a past z := by
    rw [gen_k_server_log_W_append, gen_k_server_log_T_sum hk, ← sum_add_distrib]
    refine sum_congr rfl fun x _ => ?_
    split_ifs <;> ring
  set φ := gen_k_server_log_W a past
  set Φ := ∑ z, φ z
  set φ' := gen_k_server_log_W a (past ++ [r])
  set Φ' := ∑ z, φ' z with hΦ'def
  set c : (Fin k → Fin m) → ℝ := fun x => if ∃ i, x i = r i then 0 else 1 / 2 with hc
  have hper : ∀ x, ∑ y, gen_k_server_log_P a past r x y * (hammingDist x y : ℝ) ≤ ((k : ℝ) + 1) * c x := by
    intro x
    have h1 := gen_k_server_log_K_cost hk r x
    have h2 : ∑ y, φ' y / Φ' * (hammingDist x y : ℝ) ≤ k := by
      calc _ ≤ ∑ y, φ' y / Φ' * (k : ℝ) := sum_le_sum fun y _ => by
              apply mul_le_mul_of_nonneg_left _ (div_nonneg (gen_k_server_log_W_nonneg hk a _ y) hΦ'.le)
              have := hammingDist_le_card_fintype (x := x) (y := y)
              simp only [Fintype.card_fin] at this
              exact_mod_cast this
        _ = k := by rw [← sum_mul, ← sum_div, div_self hΦ'.ne', one_mul]
    have hc0 : 0 ≤ c x := by simp only [hc]; split_ifs <;> norm_num
    calc _ = ∑ y, gen_k_server_log_K r x y * (hammingDist x y : ℝ) +
          c x * ∑ y, φ' y / Φ' * (hammingDist x y : ℝ) := by
          rw [mul_sum, ← sum_add_distrib]
          refine sum_congr rfl fun y _ => ?_
          unfold gen_k_server_log_P; simp only [hc, φ', Φ']; ring
      _ ≤ c x + c x * k := by
          apply add_le_add h1
          exact mul_le_mul_of_nonneg_left h2 hc0
      _ = _ := by ring
  calc _ = ∑ x, φ x / Φ * ∑ y, gen_k_server_log_P a past r x y * (hammingDist x y : ℝ) := by
        refine sum_congr rfl fun x _ => ?_
        rw [mul_sum]; refine sum_congr rfl fun y _ => ?_; ring
    _ ≤ ∑ x, φ x / Φ * (((k : ℝ) + 1) * c x) := sum_le_sum fun x _ =>
        mul_le_mul_of_nonneg_left (hper x) (div_nonneg (gen_k_server_log_W_nonneg hk a past x) hΦ.le)
    _ = ((k : ℝ) + 1) * (∑ x, φ x * c x) / Φ := by
        rw [mul_sum, sum_div]; refine sum_congr rfl fun x _ => ?_; ring
    _ = _ := by
        have hN : ∑ x, φ x * c x = Φ - Φ' := by linarith
        rw [hN]; field_simp

lemma gen_k_server_log_main {k m : ℕ} (hk : 1 ≤ k) (a : Fin k → Fin m) :
    ∀ (rs past : List (Fin k → Fin m)),
      gen_k_server_uniform_expected_cost_from (gen_k_server_log_P a) past
          (fun y => gen_k_server_log_W a past y / ∑ z, gen_k_server_log_W a past z) rs ≤
        ((k : ℝ) + 1) * (Real.log (∑ z, gen_k_server_log_W a past z) -
          Real.log (∑ z, gen_k_server_log_W a (past ++ rs) z)) := by
  intro rs
  induction rs with
  | nil => intro past; simp [gen_k_server_uniform_expected_cost_from]
  | cons r rs ih =>
    intro past
    simp only [gen_k_server_uniform_expected_cost_from]
    have hd : (fun y => ∑ x, gen_k_server_log_W a past x / (∑ z, gen_k_server_log_W a past z) * gen_k_server_log_P a past r x y) =
        fun y => gen_k_server_log_W a (past ++ [r]) y / ∑ z, gen_k_server_log_W a (past ++ [r]) z :=
      funext fun y => gen_k_server_log_dist hk a past r y
    rw [hd]
    have h1 := ih (past ++ [r])
    rw [List.append_assoc, List.singleton_append] at h1
    have h2 := gen_k_server_log_cost hk a past r
    have hΦ := gen_k_server_log_W_sum_pos hk a past
    have hΦ' := gen_k_server_log_W_sum_pos hk a (past ++ [r])
    have h3 : 1 - (∑ z, gen_k_server_log_W a (past ++ [r]) z) / (∑ z, gen_k_server_log_W a past z) ≤
        Real.log (∑ z, gen_k_server_log_W a past z) - Real.log (∑ z, gen_k_server_log_W a (past ++ [r]) z) := by
      have := Real.log_le_sub_one_of_pos (div_pos hΦ' hΦ)
      rw [Real.log_div hΦ'.ne' hΦ.ne'] at this
      linarith
    have hk1 : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h3 hk1]

lemma gen_k_server_log_K_self {k m : ℕ} (r u : Fin k → Fin m) (h : ∃ i, u i = r i) : gen_k_server_log_K r u u = 1 := by
  unfold gen_k_server_log_K; rw [if_pos h, if_pos rfl]

lemma gen_k_server_log_K_repair {k m : ℕ} (r u : Fin k → Fin m) (h : ¬ ∃ i, u i = r i) (i : Fin k) :
    ((2 * k : ℝ))⁻¹ ≤ gen_k_server_log_K r u (Function.update u i (r i)) := by
  open Finset in
  unfold gen_k_server_log_K
  rw [if_neg h]
  have : (1 : ℝ) ≤ ∑ j, if Function.update u i (r i) = Function.update u j (r j) then 1 else 0 := by
    have := single_le_sum (f := fun j => if Function.update u i (r i) = Function.update u j (r j)
      then (1 : ℝ) else 0) (fun j _ => by split_ifs <;> norm_num) (mem_univ i)
    simpa using this
  have h0 : (0 : ℝ) ≤ ((2 * k : ℝ))⁻¹ := by positivity
  nlinarith

lemma gen_k_server_log_offline {k m : ℕ} (hk : 1 ≤ k) (a : Fin k → Fin m) {os rs : List (Fin k → Fin m)}
    (h : List.Forall₂ (fun o r => ∃ i, o i = r i) os rs) :
    ∀ (past : List (Fin k → Fin m)) (u x0 : Fin k → Fin m),
      gen_k_server_log_W a past u ≤ (∑ z, gen_k_server_log_W a (past ++ rs) z) *
        ((2 * k : ℝ)) ^ (hammingDist u x0 + gen_k_server_uniform_path_cost x0 os) := by
  have h2k : (1 : ℝ) ≤ 2 * k := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  induction h with
  | nil =>
    intro past u x0
    simp only [List.append_nil]
    have h1 : gen_k_server_log_W a past u ≤ ∑ z, gen_k_server_log_W a past z :=
      Finset.single_le_sum (f := gen_k_server_log_W a past) (fun z _ => gen_k_server_log_W_nonneg hk a past z)
        (Finset.mem_univ u)
    have h2 : (1 : ℝ) ≤ (2 * k : ℝ) ^ (hammingDist u x0 + gen_k_server_uniform_path_cost x0 []) :=
      one_le_pow₀ h2k
    have h3 := (gen_k_server_log_W_sum_pos hk a past).le
    nlinarith
  | @cons o r os rs ho h ih =>
    intro past u x0
    simp only [gen_k_server_uniform_path_cost]
    have hend := (gen_k_server_log_W_sum_pos hk a (past ++ r :: rs)).le
    have htri := hammingDist_triangle u x0 o
    by_cases hs : ∃ i, u i = r i
    · have hih := ih (past ++ [r]) u o
      rw [List.append_assoc, List.singleton_append] at hih
      have hW : gen_k_server_log_W a past u ≤ gen_k_server_log_W a (past ++ [r]) u := by
        rw [gen_k_server_log_W_append]
        have := gen_k_server_log_T_ge r (gen_k_server_log_W a past) (gen_k_server_log_W_nonneg hk a past) u u
        rwa [gen_k_server_log_K_self r u hs, mul_one] at this
      have hpow : (2 * k : ℝ) ^ (hammingDist u o + gen_k_server_uniform_path_cost o os) ≤
          (2 * k : ℝ) ^ (hammingDist u x0 + (hammingDist x0 o + gen_k_server_uniform_path_cost o os)) :=
        pow_le_pow_right₀ h2k (by omega)
      calc _ ≤ _ := hW
        _ ≤ _ := hih
        _ ≤ _ := mul_le_mul_of_nonneg_left hpow hend
    · obtain ⟨i, hi⟩ := ho
      have hne : u i ≠ o i := by
        intro he; exact hs ⟨i, he.trans hi⟩
      set u' := Function.update u i (r i) with hu'
      have hih := ih (past ++ [r]) u' o
      rw [List.append_assoc, List.singleton_append] at hih
      have hd : hammingDist u' o + 1 = hammingDist u o := by
        rw [hu', ← hi]; exact gen_k_server_log_hd_update_succ u o i hne
      have hW : gen_k_server_log_W a past u * ((2 * k : ℝ))⁻¹ ≤ gen_k_server_log_W a (past ++ [r]) u' := by
        rw [gen_k_server_log_W_append]
        have h1 := gen_k_server_log_T_ge r (gen_k_server_log_W a past) (gen_k_server_log_W_nonneg hk a past) u u'
        have h2 := gen_k_server_log_K_repair r u hs i
        have h3 := gen_k_server_log_W_nonneg hk a past u
        nlinarith
      have hpow : (2 * k : ℝ) ^ (hammingDist u' o + gen_k_server_uniform_path_cost o os) * (2 * k) ≤
          (2 * k : ℝ) ^ (hammingDist u x0 + (hammingDist x0 o + gen_k_server_uniform_path_cost o os)) := by
        rw [← pow_succ]
        exact pow_le_pow_right₀ h2k (by omega)
      have h2kpos : (0 : ℝ) < 2 * k := by linarith
      have hW' : gen_k_server_log_W a past u ≤ gen_k_server_log_W a (past ++ [r]) u' * (2 * k) := by
        have := mul_le_mul_of_nonneg_right hW h2kpos.le
        rwa [mul_assoc, inv_mul_cancel₀ h2kpos.ne', mul_one] at this
      calc _ ≤ _ := hW'
        _ ≤ (∑ z, gen_k_server_log_W a (past ++ r :: rs) z) *
            (2 * k : ℝ) ^ (hammingDist u' o + gen_k_server_uniform_path_cost o os) * (2 * k) :=
          mul_le_mul_of_nonneg_right hih h2kpos.le
        _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hpow hend

lemma gen_k_server_log_forall₂_self {k m : ℕ} (hk : 1 ≤ k) (ρ : List (Fin k → Fin m)) :
    List.Forall₂ (fun o r => ∃ i, o i = r i) ρ ρ := by
  induction ρ with
  | nil => exact List.Forall₂.nil
  | cons r rs ih => exact List.Forall₂.cons ⟨⟨0, hk⟩, rfl⟩ ih

theorem gen_k_server_uniform_log_competitive (k m : ℕ) (hk : 1 ≤ k) (a : Fin k → Fin m) :
    ∃ P, gen_k_server_uniform_is_rand_alg P ∧ ∀ ρ : List (Fin k → Fin m),
      gen_k_server_uniform_expected_cost P a ρ ≤
        ((k : ℝ) + 1) * Real.log (2 * k) * (gen_k_server_uniform_opt a ρ : ℝ) := by
  refine ⟨gen_k_server_log_P a, gen_k_server_log_is_rand_alg hk a, fun ρ => ?_⟩
  have hW0 : gen_k_server_log_W a [] = fun x => if x = a then 1 else 0 := rfl
  have hS0 : ∑ z, gen_k_server_log_W a [] z = 1 := by rw [hW0]; simp
  have hmain := gen_k_server_log_main hk a ρ []
  rw [hS0, Real.log_one, List.nil_append] at hmain
  simp only [div_one] at hmain
  rw [hW0] at hmain
  unfold gen_k_server_uniform_expected_cost
  -- an optimal offline solution
  have hne : {c | ∃ os : List (Fin k → Fin m),
      List.Forall₂ (fun o r => ∃ i, o i = r i) os ρ ∧ gen_k_server_uniform_path_cost a os = c}.Nonempty := by
    exact ⟨_, ρ, gen_k_server_log_forall₂_self hk ρ, rfl⟩
  obtain ⟨os, hos, hcost⟩ := Nat.sInf_mem hne
  have hoff := gen_k_server_log_offline hk a hos [] a a
  rw [hW0, List.nil_append, hammingDist_self, zero_add, hcost] at hoff
  simp only [if_true] at hoff
  set ΦT := ∑ z, gen_k_server_log_W a ρ z
  have hΦT : 0 < ΦT := gen_k_server_log_W_sum_pos hk a ρ
  have h2k : (0 : ℝ) < 2 * k := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hlog : 0 ≤ Real.log ΦT + (gen_k_server_uniform_opt a ρ : ℝ) * Real.log (2 * k) := by
    have := Real.log_le_log one_pos hoff
    rw [Real.log_one, Real.log_mul hΦT.ne' (pow_pos h2k _).ne', Real.log_pow] at this
    exact this
  have hk1 : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
  unfold gen_k_server_uniform_opt at hlog ⊢
  nlinarith [mul_le_mul_of_nonneg_left hlog hk1]
