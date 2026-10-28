import AFTD.Prelude
import AFTD.Kb.Tcs.WildPartitionOfResourceBounds
import AFTD.Kb.Tcs.WildTriplePartitionLargeOrderMassBound
import AFTD.Kb.Tcs.WildNumberCompleteGraph279MinProperColoringEq
import AFTD.Kb.Tcs.WildNumberCompleteGraphMinProperColoringGe
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.G

/-!
# wild_partition_large_order_resource_bounds

Topic: graphs   Node: a0fa4eee50f4

Provenance: helper lemma. Uniform resource estimate for OP-306, extending the triple-only estimate to one or two blocks of size four. For h>=2 use two exposed binomial factors; h=1 is bounded separately at sizes 3,4,5. Experiment 7974 checks finite instances but is not used as a proof.

Suppose n is odd, q>=10000000, 3q<=n<=3q+2, and a proper n-coloring of K_n has a bijection between colors and their unique missing vertices. For any block map whose union of h blocks has between 3h and 3h+(n-3q) vertices, the displayed canonical seal-event weight sums through every position and every vertex are each at most 1/50.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
variable {q : ℕ}

def wsc_blk (hq : 3 ≤ q) (a : Fin 3) (v : Fin (3 * q + a.val)) : Fin q :=
  if h : v.val < 3 * q then ⟨v.val / 3, by omega⟩ else ⟨v.val - 3 * q, by have := a.isLt; have := v.isLt; omega⟩

def wsc_root (hq : 3 ≤ q) (a : Fin 3) (b : Fin q) : Fin (3 * q + a.val) :=
  ⟨3 * b.val, by have := b.isLt; omega⟩

lemma wsc_root_blk (hq : 3 ≤ q) (a : Fin 3) (b : Fin q) :
    wsc_blk hq a (wsc_root hq a b) = b := by
  have hb := b.isLt
  have hlt : 3*b.val < 3*q := by omega
  simp [wsc_blk, wsc_root, hlt, Fin.ext_iff]

lemma wsc_blk_fibre (hq : 3 ≤ q) (a : Fin 3) (b : Fin q) :
    (Finset.univ.filter fun v => wsc_blk hq a v = b).card = 3 + if b.val < a.val then 1 else 0 := by
  have hb := b.isLt
  have ha := a.isLt
  by_cases hba : b.val < a.val
  · have hf : (Finset.univ.filter fun v => wsc_blk hq a v = b) =
        {⟨3 * b.val, by omega⟩, ⟨3 * b.val + 1, by omega⟩,
         ⟨3 * b.val + 2, by omega⟩, ⟨3 * q + b.val, by omega⟩} := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton,
        wsc_blk, Fin.ext_iff]
      split_ifs <;> dsimp <;> omega
    rw [hf, if_pos hba]
    rw [Finset.card_insert_of_notMem (by simp [Fin.ext_iff]; omega),
      Finset.card_insert_of_notMem (by simp [Fin.ext_iff]; omega), Finset.card_pair (by simp [Fin.ext_iff]; omega)]
  · have hf : (Finset.univ.filter fun v => wsc_blk hq a v = b) =
        {⟨3 * b.val, by omega⟩, ⟨3 * b.val + 1, by omega⟩, ⟨3 * b.val + 2, by omega⟩} := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton,
        wsc_blk, Fin.ext_iff]
      split_ifs <;> dsimp <;> omega
    rw [hf, if_neg hba, Finset.card_insert_of_notMem (by simp [Fin.ext_iff]), Finset.card_pair (by simp [Fin.ext_iff])]

lemma wsc_card_pos (hq : 3 ≤ q) (a : Fin 3) (T : Finset (Fin q)) :
    (wsc_pos (wsc_blk hq a) T).card = 3 * T.card + (T.filter fun b => b.val < a.val).card := by
  classical
  have he : (wsc_pos (wsc_blk hq a) T).card = ∑ b ∈ T, (3 + if b.val < a.val then 1 else 0) := by
    rw [Finset.card_eq_sum_card_fiberwise (f := wsc_blk hq a) (t := T)]
    · refine Finset.sum_congr rfl fun b hb => ?_
      rw [← wsc_blk_fibre hq a b]
      congr 1
      ext v
      simp only [Finset.mem_filter, wsc_mem_pos, Finset.mem_univ, true_and]
      exact and_iff_right_of_imp (fun h => h ▸ hb)
    · intro v hv
      exact wsc_mem_pos.1 hv
  rw [he, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm]
  congr 1
  simp

lemma wsc_card_pos_bounds (hq : 3 ≤ q) (a : Fin 3) (T : Finset (Fin q)) :
    3 * T.card ≤ (wsc_pos (wsc_blk hq a) T).card ∧
      (wsc_pos (wsc_blk hq a) T).card ≤ 3 * T.card + a.val := by
  have hs : (T.filter fun b => b.val < a.val).card ≤ a.val := by
    calc _ ≤ (Finset.range a.val).card := by
          refine Finset.card_le_card_of_injOn Fin.val ?_ ?_
          · intro b hb
            exact Finset.mem_range.2 (Finset.mem_filter.1 hb).2
          · intro b hb b' hb' he
            exact Fin.ext he
      _ = _ := Finset.card_range _
  rw [wsc_card_pos]
  omega
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

lemma wsc_choose_cube (n q h k : ℕ) (hn : 3 * q ≤ n) (hk : 3 * h ≤ k)
    (hrem : k - 3 * h ≤ n - 3 * q) :
    q.choose h ^ 3 ≤ n.choose k := by
  have he : 1 ≤ (n - 3 * q).choose (k - 3 * h) := Nat.choose_pos hrem
  calc _ ≤ (3 * q).choose (3 * h) := wtc_choose_cube q h
    _ ≤ (3 * q).choose (3 * h) * (n - 3 * q).choose (k - 3 * h) := by nlinarith only [he]
    _ ≤ _ := by
      convert wtc_choose_mul_le (3 * q) (n - 3 * q) (3 * h) (k - 3 * h) using 1 <;> congr 1 <;> omega

noncomputable def wsc_prob (n k : ℕ) : ℝ :=
    ((n / 2).choose (k / 2) : ℝ) / (n.choose k : ℝ) * (21 / 20 : ℝ)^k

lemma wsc_prob_nonneg (n k : ℕ) : 0 ≤ wsc_prob n k := by unfold wsc_prob; positivity

lemma wsc_prob_factorial (n k : ℕ) :
    (k.factorial : ℝ) * ((n / 2).choose (k / 2) : ℝ) * wsc_wt n k = wsc_prob n k := by
  unfold wsc_wt wsc_prob
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  have hf : (k.factorial : ℝ) ≠ 0 := by positivity
  by_cases hc : (n.choose k : ℝ) = 0
  · simp [hc]
  · field_simp

lemma wsc_small_ratio (n q k : ℕ) (hq : 10000000 ≤ q)
    (hn0 : 3 * q ≤ n) (hn1 : n ≤ 3 * q + 2) (hk0 : 3 ≤ k) (hk1 : k ≤ 5) :
    ((q : ℝ) - 1) * ((q : ℝ) * ((n / 2).choose (k / 2) : ℝ) / (n.choose k : ℝ)) ≤ 8 := by
  let B : ℝ := q.choose 2
  let C : ℝ := n.choose k
  let D : ℝ := (n / 2).choose (k / 2)
  have hqR : (10000000 : ℝ) ≤ q := by exact_mod_cast hq
  have hqm : 0 < (q : ℝ)-1 := by linarith
  have hq0 : 0 < (q : ℝ) := by linarith
  have hc : 0 < C := by dsimp only [C]; exact_mod_cast Nat.choose_pos (by omega : k ≤ n)
  have hm : ((n / 2 : ℕ) : ℝ) ≤ 2 * (q : ℝ) := by exact_mod_cast (show n / 2 ≤ 2 * q by omega)
  have hb : B = (q : ℝ) * ((q : ℝ)-1) / 2 := by
    dsimp only [B]
    rw [Nat.cast_choose_two]
  have hbq : (q : ℝ) ≤ B := by rw [hb]; nlinarith
  change (q : ℝ) ≤ (q.choose 2 : ℝ) at hbq
  have hD : D ≤ 4 * (q : ℝ)^2 := by
    dsimp only [D]
    have hk2 : k / 2 = 1 ∨ k / 2 = 2 := by omega
    rcases hk2 with ht | ht
    · rw [ht, Nat.choose_one_right]
      nlinarith
    · rw [ht, Nat.cast_choose_two]
      have hm0 : (0 : ℝ) ≤ ((n / 2 : ℕ) : ℝ) := by positivity
      nlinarith
  have hbound : ((q : ℝ)-1) * (q : ℝ) * D ≤ 8 * C := by
    by_cases hk3 : k = 3
    · subst k
      have hc3 : (q : ℝ)^3 ≤ C := by
        dsimp only [C]
        have ht : q^3 ≤ n.choose 3 := by
          simpa only [Nat.choose_one_right, Nat.mul_one] using (wtc_choose_cube q 1).trans (Nat.choose_le_choose 3 hn0)
        exact_mod_cast ht
      have hd : D ≤ 2 * (q : ℝ) := by dsimp only [D]; norm_num; exact hm
      have hmul := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ ((q : ℝ)-1)*(q : ℝ))
      calc _ ≤ ((q : ℝ)-1)*(q : ℝ)*(2*(q : ℝ)) := hmul
        _ ≤ 2*(q : ℝ)^3 := by nlinarith only [sq_nonneg (q : ℝ)]
        _ ≤ 8*C := by nlinarith only [hc3, hc.le]
    · have hcn : B * (q : ℝ)^2 ≤ C := by
        have h2 := wtc_choose_mul_le q q 1 1
        have h4 := wtc_choose_mul_le q (q + q) 2 2
        have h3 := wtc_choose_mul_le q q 2 1
        have h5 := wtc_choose_mul_le q (q + q) 2 3
        have hbN : q ≤ q.choose 2 := by exact_mod_cast hbq
        have hk45 : k = 4 ∨ k = 5 := by omega
        rcases hk45 with rfl | rfl
        · dsimp only [B, C]
          exact_mod_cast (calc q.choose 2 * q^2 ≤ (3*q).choose 4 := by
                                have ht := (Nat.mul_le_mul_left (q.choose 2) h2).trans h4
                                simpa only [Nat.choose_one_right, show q+(q+q)=3*q by omega, Nat.pow_two] using ht
                              _ ≤ _ := Nat.choose_le_choose 4 hn0)
        · dsimp only [B, C]
          have h23 : q^2 ≤ (q+q).choose 3 := by
            calc _ ≤ q.choose 2 * q := by nlinarith only [Nat.mul_le_mul_right q hbN]
              _ ≤ _ := by simpa only [Nat.choose_one_right] using h3
          exact_mod_cast (calc q.choose 2 * q^2 ≤ (3*q).choose 5 := by
                                have ht := (Nat.mul_le_mul_left (q.choose 2) h23).trans h5
                                simpa only [show q+(q+q)=3*q by omega] using ht
                              _ ≤ _ := Nat.choose_le_choose 5 hn0)
      have hmul := mul_le_mul_of_nonneg_left hD (by positivity : 0 ≤ ((q : ℝ)-1)*(q : ℝ))
      rw [hb] at hcn
      nlinarith only [hmul, hcn]
  change ((q : ℝ)-1) * ((q : ℝ)*D/C) ≤ 8
  rw [← mul_div_assoc, div_le_iff₀ hc]
  simpa only [mul_assoc] using hbound

lemma wsc_mass_term_bound (n q h k : ℕ) (hq : 10000000 ≤ q)
    (hodd : n % 2 = 1) (hn0 : 3 * q ≤ n) (hn1 : n ≤ 3 * q + 2)
    (h1 : 1 ≤ h) (hh : 2 * h ≤ q) (hk0 : 3 * h ≤ k) (hk1 : k ≤ 3 * h + (n - 3 * q)) :
    (5 * h : ℝ) * (q.choose h : ℝ) * wsc_prob n k ≤
      (1 / 20000 : ℝ) * (h : ℝ)^2 * (5 / 6 : ℝ)^h := by
  have hqR : (10000000 : ℝ) ≤ q := by exact_mod_cast hq
  have hqm : 0 < (q : ℝ)-1 := by linarith
  have hk2 : k ≤ 3 * h + 2 := by omega
  by_cases heq : h = 1
  · subst h
    have hr := wsc_small_ratio n q k hq hn0 hn1 (by omega) (by omega)
    have hp : (21 / 20 : ℝ)^k ≤ 2 := by
      calc _ ≤ (21 / 20 : ℝ)^5 := pow_le_pow_right₀ (by norm_num) (by omega)
        _ ≤ _ := by norm_num
    have hn : (0 : ℝ) ≤ (q : ℝ) * ((n / 2).choose (k / 2) : ℝ) / (n.choose k : ℝ) := by positivity
    have hh := mul_le_mul hr hp (by positivity) (by norm_num : (0 : ℝ) ≤ 8)
    norm_num only [Nat.choose_one_right, Nat.cast_one, mul_one, one_pow] at *
    apply (mul_le_mul_iff_of_pos_left hqm).mp
    unfold wsc_prob
    have hsmall : (80 : ℝ) ≤ ((q : ℝ)-1) * (1 / 24000) := by linarith
    calc _ = 5 * (((q : ℝ)-1)*((q : ℝ)*((n/2).choose (k/2) : ℝ)/(n.choose k : ℝ))*(21/20 : ℝ)^k) := by ring
      _ ≤ 80 := by nlinarith only [hh]
      _ ≤ _ := hsmall
  have h2 : 2 ≤ h := by omega
  let B : ℝ := q.choose h
  let C : ℝ := n.choose k
  let D : ℝ := (n / 2).choose (k / 2)
  have hb : 0 < B := by dsimp only [B]; exact_mod_cast Nat.choose_pos (by omega : h ≤ q)
  have hc : 0 < C := by dsimp only [C]; exact_mod_cast Nat.choose_pos (by omega : k ≤ n)
  have hd : 0 ≤ D := by positivity
  have hb3 : B^3 ≤ C := by
    dsimp only [B, C]
    exact_mod_cast wsc_choose_cube n q h k hn0 hk0 (by omega)
  have hnn : 2 * (n / 2) + 1 = n := by omega
  have hd2 : D^2 ≤ C := by
    dsimp only [D, C]
    exact_mod_cast (hnn ▸ wtc_choose_square (n / 2) k)
  have hchoose : (q : ℝ) * ((q : ℝ) - 1) * 2^(h-2) ≤ (h : ℝ) * ((h : ℝ) - 1) * B := by
    dsimp only [B]
    have ht : ((q * (q - 1) * 2 ^ (h - 2) : ℕ) : ℝ) ≤
        ((h * (h - 1) * q.choose h : ℕ) : ℝ) := by exact_mod_cast wtc_choose_lower_two q h h2 hh
    simp only [Nat.cast_mul] at ht
    rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_sub (by omega : 1 ≤ h)] at ht
    simpa using ht
  have hhR : 2 ≤ (h : ℝ) := by exact_mod_cast h2
  have hhm : 0 ≤ (h : ℝ)-1 := by linarith
  have hbase : (21 / 20 : ℝ)^6 ≤ 2 * (5 / 6 : ℝ)^2 := by norm_num
  have hpw := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (21 / 20)^6) hbase h
  have hp0 : ((21 / 20 : ℝ)^(3*h))^2 ≤ 2^h*((5/6 : ℝ)^h)^2 := by
    have he1 : 3*h*2=6*h := by omega
    have he2 : 2*h=h*2 := by omega
    simpa only [mul_pow, ← pow_mul, he1, he2] using hpw
  have hpweq : ((21 / 20 : ℝ)^k)^2 ≤ 2 * 2^h * ((5 / 6 : ℝ)^h)^2 := by
    have hkpow : (21 / 20 : ℝ)^k ≤ (21/20)^(3*h+2) := pow_le_pow_right₀ (by norm_num) hk2
    have hkp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (21/20)^k) hkpow 2
    have he : ((21 / 20 : ℝ)^(3*h+2))^2 = (21/20)^4 * ((21/20)^(3*h))^2 := by rw [pow_add]; ring
    rw [he] at hkp
    have hp4 : (21 / 20 : ℝ)^4 ≤ 2 := by norm_num
    exact hkp.trans (by nlinarith only [mul_le_mul hp4 hp0 (by positivity) (by norm_num : (0 : ℝ) ≤ 2)])
  have h2pow : (2 : ℝ)^h = 4 * (2 : ℝ)^(h-2) := by
    calc (2 : ℝ)^h = 2^(h-2+2) := by congr 1; omega
      _ = _ := by rw [pow_add]; norm_num; ring
  have hratio : B * (B * D / C)^2 ≤ 1 := by
    have hmul : B^3 * D^2 ≤ C^2 := by
      simpa only [pow_two] using mul_le_mul hb3 hd2 (by positivity : 0 ≤ D^2) (by positivity : 0 ≤ C)
    have he : B * (B * D / C)^2 = (B^3 * D^2) / C^2 := by ring
    rw [he, div_le_one (sq_pos_of_pos hc)]
    exact hmul
  have hratio' : (q : ℝ) * ((q : ℝ)-1) * 2^(h-2) * (B * D / C)^2 ≤ (h : ℝ) * ((h : ℝ)-1) := by
    calc _ ≤ ((h : ℝ) * ((h : ℝ)-1) * B) * (B * D / C)^2 := mul_le_mul_of_nonneg_right hchoose (sq_nonneg _)
      _ = (h : ℝ) * ((h : ℝ)-1) * (B * (B * D / C)^2) := by ring
      _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ (h : ℝ)*((h : ℝ)-1))
  have hs := mul_le_mul hratio' hpweq (by positivity) (by positivity : 0 ≤ (h : ℝ)*((h : ℝ)-1))
  rw [h2pow] at hs
  have hs' : (q : ℝ)*((q : ℝ)-1)*(B*D/C)^2*((21/20 : ℝ)^k)^2 ≤
      8*(h : ℝ)*((h : ℝ)-1)*((5/6 : ℝ)^h)^2 := by
    apply (mul_le_mul_iff_of_pos_left (by positivity : (0 : ℝ) < 2^(h-2))).mp
    nlinarith only [hs]
  have hquot : ((5*h : ℝ)*(q.choose h : ℝ)*wsc_prob n k)^2 =
      25*(h : ℝ)^2*(B*D/C)^2*((21/20 : ℝ)^k)^2 := by dsimp [wsc_prob, B, C, D]; push_cast; ring
  have hupper : (q : ℝ)*((q : ℝ)-1)*((5*h : ℝ)*(q.choose h : ℝ)*wsc_prob n k)^2 ≤
      200*(h : ℝ)^4*((5/6 : ℝ)^h)^2 := by
    rw [hquot]
    have hm1 := mul_le_mul_of_nonneg_left hs' (by positivity : 0 ≤ 25*(h : ℝ)^2)
    have hhh : (h : ℝ)*((h : ℝ)-1) ≤ (h : ℝ)^2 := by nlinarith
    have hm2 := mul_le_mul_of_nonneg_left hhh (by positivity : 0 ≤ 200*(h : ℝ)^2*((5/6 : ℝ)^h)^2)
    nlinarith only [hm1, hm2]
  have hqq : (80000000000 : ℝ) ≤ (q : ℝ)*((q : ℝ)-1) := by nlinarith [sq_nonneg ((q : ℝ)-10000000)]
  have hsq : ((5*h : ℝ)*(q.choose h : ℝ)*wsc_prob n k)^2 ≤
      ((1 / 20000 : ℝ)*(h : ℝ)^2*(5/6 : ℝ)^h)^2 := by
    apply (mul_le_mul_iff_of_pos_left (by positivity : (0 : ℝ) < (q : ℝ)*((q : ℝ)-1))).mp
    calc _ ≤ 200*(h : ℝ)^4*((5/6 : ℝ)^h)^2 := hupper
      _ ≤ _ := by
        have hx := mul_le_mul_of_nonneg_right hqq (by positivity : 0 ≤ ((1 / 20000 : ℝ)*(h : ℝ)^2*(5/6 : ℝ)^h)^2)
        nlinarith only [hx]
  have hnon : 0 ≤ (1 / 20000 : ℝ)*(h : ℝ)^2*(5/6 : ℝ)^h := by positivity
  nlinarith [sq_nonneg ((5*h : ℝ)*(q.choose h : ℝ)*wsc_prob n k + (1 / 20000 : ℝ)*(h : ℝ)^2*(5/6 : ℝ)^h)]

noncomputable def wsc_phi (q h : ℕ) : ℝ :=
  ((1 / 20000 : ℝ)*(h : ℝ)^2*(5/6 : ℝ)^h) / ((5*h : ℝ)*(q.choose h : ℝ))

lemma wsc_phi_nonneg (q h : ℕ) : 0 ≤ wsc_phi q h := by unfold wsc_phi; positivity

lemma wsc_prob_le_phi (n q h k : ℕ) (hq : 10000000 ≤ q)
    (hodd : n % 2 = 1) (hn0 : 3 * q ≤ n) (hn1 : n ≤ 3 * q + 2)
    (h1 : 1 ≤ h) (hh : 2 * h ≤ q) (hk0 : 3 * h ≤ k) (hk1 : k ≤ 3 * h + (n - 3 * q)) :
    wsc_prob n k ≤ wsc_phi q h := by
  have hb : 0 < (q.choose h : ℝ) := by exact_mod_cast Nat.choose_pos (by omega : h ≤ q)
  unfold wsc_phi
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < (5*h : ℝ)*(q.choose h : ℝ))]
  nlinarith only [wsc_mass_term_bound n q h k hq hodd hn0 hn1 h1 hh hk0 hk1]

lemma wsc_phi_cancel (q h : ℕ) (h1 : 1 ≤ h) (hh : h ≤ q) :
    (5*h : ℝ) * (q.choose h : ℝ) * wsc_phi q h =
      (1/20000 : ℝ)*(h : ℝ)^2*(5/6 : ℝ)^h := by
  have hb : (q.choose h : ℝ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hh
  have hhh : (h : ℝ) ≠ 0 := by exact_mod_cast (by omega : h ≠ 0)
  unfold wsc_phi
  field_simp

lemma wsc_position_phi_bound (n q h : ℕ) (hq : 10000000 ≤ q) (hn : n ≤ 3*q+2)
    (h1 : 1 ≤ h) (hh : 2*h ≤ q) :
    (n : ℝ) * ((q-1).choose (h-1) : ℝ) * wsc_phi q h ≤
      (1/20000 : ℝ)*(h : ℝ)^2*(5/6 : ℝ)^h := by
  have hi := Nat.add_one_mul_choose_eq (q-1) (h-1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ q), Nat.sub_add_cancel h1] at hi
  have hir : (q : ℝ) * ((q-1).choose (h-1) : ℝ) = (q.choose h : ℝ) * (h : ℝ) := by exact_mod_cast hi
  have hnr : (n : ℝ) ≤ 5*(q : ℝ) := by exact_mod_cast (show n ≤ 5*q by omega)
  calc _ ≤ 5*(q : ℝ) * ((q-1).choose (h-1) : ℝ) * wsc_phi q h := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hnr (by positivity)) (wsc_phi_nonneg _ _)
    _ = (5*h : ℝ)*(q.choose h : ℝ)*wsc_phi q h := by rw [mul_assoc 5, hir]; ring
    _ = _ := wsc_phi_cancel q h h1 (by omega)

lemma wsc_geometric_bound (q : ℕ) :
    ∑ h ∈ Finset.range (q+1), (1/20000 : ℝ)*(h : ℝ)^2*(5/6 : ℝ)^h ≤ 1/50 := by
  have hi := wtc_geometric_square_sum (q+1)
  simp only [mul_assoc]
  rw [← Finset.mul_sum]
  nlinarith

lemma wsc_shifted_geometric_bound (q : ℕ) :
    ∑ h ∈ Finset.range q, (1/20000 : ℝ)*((h+1 : ℕ) : ℝ)^2*(5/6 : ℝ)^(h+1) ≤ 1/50 := by
  have hi := wsc_geometric_bound q
  rw [Finset.sum_range_succ'] at hi
  norm_num at hi
  simpa only [Nat.cast_add, Nat.cast_one] using hi
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
variable {n q : ℕ}

lemma wsc_R_card
    (c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin n)) (m : Fin n ≃ Fin n)
    (hm : ∀ (i v : Fin n), (∀ w (hvw : v ≠ w), c ⟨s(v, w), wild_kn_mem hvw⟩ ≠ i) ↔ v = m i)
    (i : Fin n) : (w279_R c m i).card = n / 2 := by
  have := w279_card_R c m hm i
  omega

theorem wsc_fibre_card (b : Fin n → Fin q) (i : Fin n) (T : Finset (Fin q)) (P : Finset (Fin n) → Prop) [DecidablePred P]
    (Fsel : Finset (Fin n × Finset (Fin q) × (Fin n → Fin n)))
    (hF : ∀ t ∈ Fsel, t.1 = i → t.2.1 = T → (∀ v ∉ wsc_pos b t.2.1, t.2.2 v = v) ∧ Set.InjOn t.2.2 ↑(wsc_pos b t.2.1) ∧
      P ((wsc_pos b t.2.1).image t.2.2)) :
    (Fsel.filter fun t => (t.1, t.2.1) = (i, T)).card ≤ (wsc_pos b T).card.factorial *
      (Finset.univ.filter fun U : Finset (Fin n) => U.card = (wsc_pos b T).card ∧ P U).card := by
  classical
  refine le_trans ?_ (w279_count_events (wsc_pos b T) P)
  refine Finset.card_le_card_of_injOn (fun t => t.2.2) ?_ ?_
  · intro t ht
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Prod.mk.injEq] at ht
    obtain ⟨ht, h1, h2⟩ := ht
    obtain ⟨g1, g2, g3⟩ := hF t ht h1 h2
    rw [h2] at g1 g2 g3
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    exact ⟨g1, g2, g3⟩
  · intro t ht t' ht' h
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Prod.mk.injEq] at ht ht'
    obtain ⟨-, h1, h2⟩ := ht
    obtain ⟨-, h1', h2'⟩ := ht'
    exact Prod.ext (h1.trans h1'.symm) (Prod.ext (h2.trans h2'.symm) h)


theorem wsc_pos_mass (hq : 10000000 ≤ q) (hodd : n % 2 = 1) (hn0 : 3*q ≤ n) (hn1 : n ≤ 3*q+2)
    (b : Fin n → Fin q)
    (hblock : ∀ T : Finset (Fin q), 3*T.card ≤ (wsc_pos b T).card ∧ (wsc_pos b T).card ≤ 3*T.card+(n-3*q))
    (c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin n)) (m : Fin n ≃ Fin n)
    (hm : ∀ (i v : Fin n), (∀ w (hvw : v ≠ w), c ⟨s(v, w), wild_kn_mem hvw⟩ ≠ i) ↔ v = m i) (p : Fin n) :
    ∑ t ∈ (wsc_E b c).filter (fun t => p ∈ wsc_pos b t.2.1),
      wsc_wt n (wsc_pos b t.2.1).card ≤ 1/50 := by
  classical
  set Fsel := (wsc_E b c).filter (fun t => p ∈ wsc_pos b t.2.1) with hFdef
  have hFmem : ∀ t ∈ Fsel, (1 ≤ t.2.1.card ∧ t.2.1.card ≤ (q / 2) ∧ b p ∈ t.2.1) ∧
      ((∀ v ∉ wsc_pos b t.2.1, t.2.2 v = v) ∧ Set.InjOn t.2.2 ↑(wsc_pos b t.2.1) ∧
      w279_closed c t.1 ((wsc_pos b t.2.1).image t.2.2)) := by
    intro t ht
    rw [hFdef, Finset.mem_filter, wsc_mem_E ] at ht
    exact ⟨⟨ht.1.1, ht.1.2.1, wsc_mem_pos.1 ht.2⟩, ht.1.2.2⟩
  let 𝒯 : Finset (Finset (Fin q)) := Finset.univ.filter fun T => 1 ≤ T.card ∧ T.card ≤ (q / 2) ∧ b p ∈ T
  let φ : ℕ → ℝ := wsc_phi q
  have step1 : ∑ t ∈ Fsel, wsc_wt n (wsc_pos b t.2.1).card ≤ ∑ x ∈ (Finset.univ : Finset (Fin n)) ×ˢ 𝒯, φ x.2.card := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun t => (t.1, t.2.1)) (t := Finset.univ ×ˢ 𝒯)]
    · refine Finset.sum_le_sum fun x hx => ?_
      have hw : ∀ t ∈ Fsel.filter (fun t => (t.1, t.2.1) = x), wsc_wt n (wsc_pos b t.2.1).card = wsc_wt n (wsc_pos b x.2).card := by
        intro t ht
        rw [Finset.mem_filter] at ht
        rw [← ht.2]
      rw [Finset.sum_congr rfl hw, Finset.sum_const, nsmul_eq_mul]
      have hc := wsc_fibre_card b x.1 x.2 (fun U => w279_closed c x.1 U) Fsel ?_
      · have hc2 := w279_count_closed c m hm x.1 (wsc_pos b x.2).card
        rw [wsc_R_card c m hm] at hc2
        have hc3 : (Fsel.filter fun t => (t.1, t.2.1) = x).card ≤ (wsc_pos b x.2).card.factorial * Nat.choose (n / 2) ((wsc_pos b x.2).card / 2) := by
          refine le_trans hc (Nat.mul_le_mul_left _ (le_trans (Finset.card_le_card ?_) hc2))
          intro U hU
          simp only [Finset.mem_filter] at hU ⊢
          exact hU
        have hT := (Finset.mem_filter.1 (Finset.mem_product.1 hx).2).2
        have hb := hblock x.2
        have hcR : ((Fsel.filter fun t => (t.1, t.2.1) = x).card : ℝ) ≤
            (((wsc_pos b x.2).card.factorial * Nat.choose (n/2) ((wsc_pos b x.2).card/2) : ℕ) : ℝ) := by exact_mod_cast hc3
        calc _ ≤ _ := mul_le_mul_of_nonneg_right hcR (wsc_wt_nonneg n _)
          _ = wsc_prob n (wsc_pos b x.2).card := by push_cast; exact wsc_prob_factorial n _
          _ ≤ φ x.2.card := wsc_prob_le_phi n q x.2.card (wsc_pos b x.2).card hq hodd hn0 hn1
            hT.1 (by omega) hb.1 (by have := hb.2; omega)

      · intro t ht hi _
        obtain ⟨-, h1, h2, h3⟩ := hFmem t ht
        exact ⟨h1, h2, by rw [← hi]; exact h3⟩
    · intro t ht
      obtain ⟨h0, -⟩ := hFmem t ht
      exact Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_filter.2 ⟨Finset.mem_univ _, h0⟩⟩
  have step2 : ∑ x ∈ (Finset.univ : Finset (Fin n)) ×ˢ 𝒯, φ x.2.card = n * ∑ T ∈ 𝒯, φ T.card := by
    rw [Finset.sum_product]
    dsimp only
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have step3 : ∑ T ∈ 𝒯, φ T.card = ∑ m ∈ Finset.range q, ((Nat.choose (q - 1) m : ℕ) : ℝ) *
      (if m + 1 ≤ (q / 2) then φ (m + 1) else 0) := by
    set b := b p
    have hcard : (Finset.univ.erase b).card = (q - 1) := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    have e1 : ∑ T ∈ 𝒯, φ T.card = ∑ T' ∈ (Finset.univ.erase b).powerset.filter (fun T' => T'.card + 1 ≤ (q / 2)),
        φ (T'.card + 1) := by
      refine Finset.sum_nbij' (fun T => T.erase b) (fun T' => insert b T') ?_ ?_ ?_ ?_ ?_
      · intro T hT
        simp only [𝒯, Finset.mem_filter, Finset.mem_univ, true_and] at hT
        simp only [Finset.mem_filter, Finset.mem_powerset]
        refine ⟨Finset.erase_subset_erase _ (Finset.subset_univ _), ?_⟩
        rw [Finset.card_erase_add_one hT.2.2]; exact hT.2.1
      · intro T' hT'
        simp only [Finset.mem_filter, Finset.mem_powerset] at hT'
        have hb : b ∉ T' := fun h => by simpa using hT'.1 h
        simp only [𝒯, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [Finset.card_insert_of_notMem hb]
        exact ⟨by omega, hT'.2, Finset.mem_insert_self _ _⟩
      · intro T hT
        simp only [𝒯, Finset.mem_filter, Finset.mem_univ, true_and] at hT
        exact Finset.insert_erase hT.2.2
      · intro T' hT'
        simp only [Finset.mem_filter, Finset.mem_powerset] at hT'
        have hb : b ∉ T' := fun h => by simpa using hT'.1 h
        exact Finset.erase_insert hb
      · intro T hT
        simp only [𝒯, Finset.mem_filter, Finset.mem_univ, true_and] at hT
        rw [Finset.card_erase_add_one hT.2.2]
    rw [e1, Finset.sum_filter]
    have := Finset.sum_powerset_apply_card (fun m => if m + 1 ≤ (q / 2) then φ (m + 1) else 0)
      (x := Finset.univ.erase b)
    rw [hcard, Nat.sub_add_cancel (by omega : 1 ≤ q)] at this
    rw [this]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [nsmul_eq_mul]
  calc _ ≤ _ := step1
    _ = _ := by rw [step2, step3]
    _ ≤ ∑ h ∈ Finset.range q, (1/20000 : ℝ)*((h+1 : ℕ) : ℝ)^2*(5/6 : ℝ)^(h+1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun h hh => ?_
      by_cases hh' : h + 1 ≤ q / 2
      · rw [if_pos hh']
        simpa only [φ, Nat.add_sub_cancel, mul_assoc] using
          wsc_position_phi_bound n q (h+1) hq hn1 (by omega) (by omega)
      · rw [if_neg hh', mul_zero, mul_zero]
        positivity
    _ ≤ 1/50 := wsc_shifted_geometric_bound q

theorem wsc_vert_mass (hq : 10000000 ≤ q) (hodd : n % 2 = 1) (hn0 : 3*q ≤ n) (hn1 : n ≤ 3*q+2)
    (b : Fin n → Fin q)
    (hblock : ∀ T : Finset (Fin q), 3*T.card ≤ (wsc_pos b T).card ∧ (wsc_pos b T).card ≤ 3*T.card+(n-3*q))
    (c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin n)) (m : Fin n ≃ Fin n)
    (hm : ∀ (i v : Fin n), (∀ w (hvw : v ≠ w), c ⟨s(v, w), wild_kn_mem hvw⟩ ≠ i) ↔ v = m i) (w : Fin n) :
    ∑ t ∈ (wsc_E b c).filter (fun t => w ∈ (wsc_pos b t.2.1).image t.2.2),
      wsc_wt n (wsc_pos b t.2.1).card ≤ 1/50 := by
  classical
  set Fsel := (wsc_E b c).filter (fun t => w ∈ (wsc_pos b t.2.1).image t.2.2) with hFdef
  have hFmem : ∀ t ∈ Fsel, (1 ≤ t.2.1.card ∧ t.2.1.card ≤ (q / 2)) ∧
      ((∀ v ∉ wsc_pos b t.2.1, t.2.2 v = v) ∧ Set.InjOn t.2.2 ↑(wsc_pos b t.2.1) ∧
      (w279_closed c t.1 ((wsc_pos b t.2.1).image t.2.2) ∧ w ∈ (wsc_pos b t.2.1).image t.2.2)) := by
    intro t ht
    rw [hFdef, Finset.mem_filter, wsc_mem_E ] at ht
    exact ⟨⟨ht.1.1, ht.1.2.1⟩, ht.1.2.2.1, ht.1.2.2.2.1, ht.1.2.2.2.2, ht.2⟩
  let 𝒯 : Finset (Finset (Fin q)) := Finset.univ.filter fun T => 1 ≤ T.card ∧ T.card ≤ (q / 2)
  let X : ℕ → ℕ := fun s => if s % 2 = 1 then Nat.choose (n / 2) (s / 2) else 0
  let Y : ℕ → ℕ := fun s => Nat.choose (n / 2 - 1) (s / 2 - 1)
  let bnd : Fin n → ℕ → ℝ := fun i s => (s.factorial : ℝ) * (if m i = w then (X s : ℝ) else (Y s : ℝ))
  have step1 : ∑ t ∈ Fsel, wsc_wt n (wsc_pos b t.2.1).card ≤
      ∑ x ∈ (Finset.univ : Finset (Fin n)) ×ˢ 𝒯, bnd x.1 (wsc_pos b x.2).card * wsc_wt n (wsc_pos b x.2).card := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun t => (t.1, t.2.1)) (t := Finset.univ ×ˢ 𝒯)]
    · refine Finset.sum_le_sum fun x hx => ?_
      have hw : ∀ t ∈ Fsel.filter (fun t => (t.1, t.2.1) = x), wsc_wt n (wsc_pos b t.2.1).card = wsc_wt n (wsc_pos b x.2).card := by
        intro t ht
        rw [Finset.mem_filter] at ht
        rw [← ht.2]
      rw [Finset.sum_congr rfl hw, Finset.sum_const, nsmul_eq_mul]
      have hc := wsc_fibre_card b x.1 x.2 (fun U => w279_closed c x.1 U ∧ w ∈ U) Fsel ?_
      · have hc2 : (Finset.univ.filter fun U : Finset (Fin n) => U.card = (wsc_pos b x.2).card ∧
            (w279_closed c x.1 U ∧ w ∈ U)).card ≤ if m x.1 = w then X (wsc_pos b x.2).card else Y (wsc_pos b x.2).card := by
          split_ifs with hmw
          · have := w279_count_closed_mem_m c m hm x.1 (wsc_pos b x.2).card
            rw [wsc_R_card c m hm, hmw] at this
            exact this
          · have := w279_count_closed_mem c m hm x.1 (wsc_pos b x.2).card w (Ne.symm hmw)
            rw [wsc_R_card c m hm] at this
            exact this
        have hc3 : ((Fsel.filter fun t => (t.1, t.2.1) = x).card : ℝ) ≤ bnd x.1 (wsc_pos b x.2).card := by
          have h4 : (Fsel.filter fun t => (t.1, t.2.1) = x).card ≤ (wsc_pos b x.2).card.factorial *
              (if m x.1 = w then X (wsc_pos b x.2).card else Y (wsc_pos b x.2).card) := by
            refine le_trans hc (Nat.mul_le_mul_left _ (le_trans (Finset.card_le_card ?_) hc2))
            intro U hU
            simp only [Finset.mem_filter] at hU ⊢
            exact hU
          simp only [bnd]
          split_ifs at h4 ⊢ <;> exact_mod_cast h4
        exact mul_le_mul_of_nonneg_right hc3 (wsc_wt_nonneg n  _)
      · intro t ht hi _
        obtain ⟨-, h1, h2, h3, h4⟩ := hFmem t ht
        exact ⟨h1, h2, by rw [← hi]; exact h3, h4⟩
    · intro t ht
      obtain ⟨h0, -⟩ := hFmem t ht
      exact Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_filter.2 ⟨Finset.mem_univ _, h0⟩⟩
  have hsumcol : ∀ s, ∑ i : Fin n, bnd i s = (((s.factorial * X s + (n - 1) * (s.factorial * Y s)) : ℕ) : ℝ) := by
    intro s
    have h1 : (Finset.univ.filter fun i : Fin n => m i = w) = {m.symm w} := by
      ext i; simp [Equiv.apply_eq_iff_eq_symm_apply]
    have h2 : (Finset.univ.filter fun i : Fin n => ¬ m i = w).card = (n - 1) := by
      have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
        (p := fun i => m i = w)
      rw [h1, Finset.card_singleton, Finset.card_univ, Fintype.card_fin] at this
      omega
    simp only [bnd, mul_ite]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, h1, h2, Finset.card_singleton]
    push_cast
    ring
  have step2 : ∑ x ∈ (Finset.univ : Finset (Fin n)) ×ˢ 𝒯, bnd x.1 (wsc_pos b x.2).card * wsc_wt n (wsc_pos b x.2).card =
      ∑ T ∈ 𝒯, (((wsc_pos b T).card.factorial * X (wsc_pos b T).card + (n - 1) * ((wsc_pos b T).card.factorial * Y (wsc_pos b T).card) : ℕ) : ℝ)
        * wsc_wt n (wsc_pos b T).card := by
    rw [Finset.sum_product, Finset.sum_comm]
    refine Finset.sum_congr rfl fun T _ => ?_
    dsimp only
    rw [← Finset.sum_mul, hsumcol]
  have step3 : ∑ T ∈ 𝒯,
        ((((wsc_pos b T).card.factorial * X (wsc_pos b T).card + (n-1) * ((wsc_pos b T).card.factorial * Y (wsc_pos b T).card)) : ℕ) : ℝ)
          * wsc_wt n (wsc_pos b T).card ≤ ∑ T ∈ 𝒯, (5*T.card : ℝ)*wsc_phi q T.card := by
    refine Finset.sum_le_sum fun T hT => ?_
    have hT' := (Finset.mem_filter.1 hT).2
    have hb := hblock T
    have hk3 : 3 ≤ (wsc_pos b T).card := by omega
    have hi := wtc_vertex_coefficient n (wsc_pos b T).card hodd (by omega) hk3
    have hi' : (wsc_pos b T).card.factorial * X (wsc_pos b T).card +
        (n-1) * ((wsc_pos b T).card.factorial * Y (wsc_pos b T).card) =
        (wsc_pos b T).card.factorial * ((wsc_pos b T).card * (n/2).choose ((wsc_pos b T).card/2)) := by
      dsimp only [X, Y]
      nlinarith only [congrArg (fun z => (wsc_pos b T).card.factorial*z) hi]
    rw [hi']
    push_cast
    have he : ((wsc_pos b T).card.factorial : ℝ) * ((wsc_pos b T).card : ℝ) *
        ((n/2).choose ((wsc_pos b T).card/2) : ℝ) * wsc_wt n (wsc_pos b T).card =
        ((wsc_pos b T).card : ℝ)*wsc_prob n (wsc_pos b T).card := by
      rw [← wsc_prob_factorial]
      ring
    rw [← mul_assoc, he]
    have hp := wsc_prob_le_phi n q T.card (wsc_pos b T).card hq hodd hn0 hn1
      hT'.1 (by omega) hb.1 (by have := hb.2; omega)
    have hk : ((wsc_pos b T).card : ℝ) ≤ (5*T.card : ℝ) := by exact_mod_cast (show (wsc_pos b T).card ≤ 5*T.card by have := hb.2; omega)
    exact mul_le_mul hk hp (wsc_prob_nonneg _ _) (by positivity)
  have step4 : (∑ T ∈ 𝒯, (5*T.card : ℝ)*wsc_phi q T.card) =
      ∑ h ∈ Finset.range (q+1), (q.choose h : ℝ) *
        (if 1 ≤ h ∧ h ≤ q/2 then (5*h : ℝ)*wsc_phi q h else 0) := by
    rw [Finset.sum_filter, ← Finset.powerset_univ]
    have he := Finset.sum_powerset_apply_card
      (fun h => if 1 ≤ h ∧ h ≤ q/2 then (5*h : ℝ)*wsc_phi q h else 0)
      (x := (Finset.univ : Finset (Fin q)))
    rw [Finset.card_univ, Fintype.card_fin] at he
    rw [he]
    refine Finset.sum_congr rfl fun h hh => ?_
    rw [nsmul_eq_mul]
  calc _ ≤ _ := step1
    _ = _ := step2
    _ ≤ _ := step3
    _ = _ := step4
    _ ≤ ∑ h ∈ Finset.range (q+1), (1/20000 : ℝ)*(h : ℝ)^2*(5/6 : ℝ)^h := by
      refine Finset.sum_le_sum fun h hh => ?_
      by_cases hh' : 1 ≤ h ∧ h ≤ q/2
      · rw [if_pos hh']
        have hi := wsc_phi_cancel q h hh'.1 (by omega)
        nlinarith only [hi]
      · rw [if_neg hh', mul_zero]
        positivity
    _ ≤ 1/50 := wsc_geometric_bound q

theorem wild_partition_large_order_resource_bounds {n q : ℕ} (hq : 10000000 ≤ q) (hodd : n % 2 = 1) (hn0 : 3*q ≤ n) (hn1 : n ≤ 3*q+2)
    (b : Fin n → Fin q)
    (hblock : ∀ T : Finset (Fin q), 3*T.card ≤ (wsc_pos b T).card ∧ (wsc_pos b T).card ≤ 3*T.card+(n-3*q))
    (c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin n)) (m : Fin n ≃ Fin n)
    (hm : ∀ (i v : Fin n), (∀ w (hvw : v ≠ w), c ⟨s(v, w), wild_kn_mem hvw⟩ ≠ i) ↔ v = m i) :
    (∀ p : Fin n, ∑ t ∈ (wsc_E b c).filter (fun t => p ∈ wsc_pos b t.2.1),
      wsc_wt n (wsc_pos b t.2.1).card ≤ 1/50) ∧
    (∀ w : Fin n, ∑ t ∈ (wsc_E b c).filter (fun t => w ∈ (wsc_pos b t.2.1).image t.2.2),
      wsc_wt n (wsc_pos b t.2.1).card ≤ 1/50) := by
  exact ⟨wsc_pos_mass hq hodd hn0 hn1 b hblock c m hm, wsc_vert_mass hq hodd hn0 hn1 b hblock c m hm⟩
