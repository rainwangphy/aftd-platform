import AFTD.Prelude
import AFTD.Kb.Tcs.WildTriplePartitionMassCriterion
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# wild_triple_partition_large_order_mass_bound

Topic: graphs   Node: 9a444c70fe89

Provenance: helper lemma. Uniform arithmetic estimate for OP-306. Vandermonde bounds give C(q,h)^3 <= C(3q,3h) and C(floor(3q/2),floor(3h/2))^2 <= C(3q,3h). Two exposed binomial factors and the geometric-square sum 330 give the threshold.

For odd q>=100001, both canonical seal-event resource sums for q triples of vertices in K_(3q), with weight (21/20)^d/(3q)_d, are at most 1/50.
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

lemma wtc_choose_mul_le (a b i j : ℕ) :
    a.choose i * b.choose j ≤ (a + b).choose (i + j) := by
  rw [Nat.add_choose_eq]
  exact Finset.single_le_sum (a := (i, j)) (f := fun ij : ℕ × ℕ => a.choose ij.1 * b.choose ij.2) (fun _ _ => Nat.zero_le _)
    (Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl)

lemma wtc_choose_cube (q h : ℕ) :
    q.choose h ^ 3 ≤ (3 * q).choose (3 * h) := by
  have h1 := wtc_choose_mul_le q q h h
  have h2 := wtc_choose_mul_le (q + q) q (h + h) h
  calc _ = (q.choose h * q.choose h) * q.choose h := by ring
    _ ≤ (q + q).choose (h + h) * q.choose h := Nat.mul_le_mul_right _ h1
    _ ≤ _ := by convert h2 using 1 <;> congr 1 <;> omega

lemma wtc_choose_square (m s : ℕ) :
    m.choose (s / 2) ^ 2 ≤ (2 * m + 1).choose s := by
  have hs : s = s / 2 + (s / 2 + s % 2) := by omega
  have hc : m.choose (s / 2) ≤ (m + 1).choose (s / 2 + s % 2) := by
    have hmod := Nat.mod_lt s (by omega : 0 < 2)
    interval_cases hm : s % 2
    · simpa [hm] using Nat.choose_le_succ m (s / 2)
    · rw [Nat.choose_succ_succ]
      omega
  calc _ = m.choose (s / 2) * m.choose (s / 2) := by ring
    _ ≤ m.choose (s / 2) * (m + 1).choose (s / 2 + s % 2) := Nat.mul_le_mul_left _ hc
    _ ≤ _ := by
      convert wtc_choose_mul_le m (m + 1) (s / 2) (s / 2 + s % 2) using 1 <;> congr 1 <;> omega

lemma wtc_two_pow_le_choose (q h : ℕ) (hh : 2 * h ≤ q) : 2 ^ h ≤ q.choose h := by
  induction h generalizing q with
  | zero => simp
  | succ h ih =>
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
    have hi := ih q (by omega)
    have he := Nat.add_one_mul_choose_eq q h
    have hz : 0 < h + 1 := by omega
    apply Nat.le_of_mul_le_mul_right (c := h + 1) (hc := hz)
    calc 2 ^ (h + 1) * (h + 1) = (2 * (h + 1)) * 2 ^ h := by rw [pow_succ]; ring
      _ ≤ (q + 1) * 2 ^ h := Nat.mul_le_mul_right _ hh
      _ ≤ (q + 1) * q.choose h := Nat.mul_le_mul_left _ hi
      _ = _ := he

lemma wtc_choose_lower (q h : ℕ) (h1 : 1 ≤ h) (hh : 2 * h ≤ q) :
    q * 2 ^ (h - 1) ≤ h * q.choose h := by
  obtain ⟨h, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : h ≠ 0)
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  have hi := wtc_two_pow_le_choose q h (by omega)
  simpa [Nat.mul_comm] using (Nat.mul_le_mul_left (q + 1) hi).trans_eq (Nat.add_one_mul_choose_eq q h)

lemma wtc_geometric_square_sum (n : ℕ) :
    ∑ h ∈ Finset.range n, (h : ℝ)^2 * (5 / 6 : ℝ)^h ≤ 330 := by
  have heq : ∀ n : ℕ, (∑ h ∈ Finset.range n, (h : ℝ)^2 * (5 / 6 : ℝ)^h) +
      (6 * (n : ℝ)^2 + 60 * n + 330) * (5 / 6 : ℝ)^n = 330 := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [Finset.sum_range_succ]
      push_cast
      rw [pow_succ (5 / 6 : ℝ) n]
      nlinarith only [ih]
  have hp : 0 ≤ (6 * (n : ℝ)^2 + 60 * n + 330) * (5 / 6 : ℝ)^n := by positivity
  linarith [heq n]

noncomputable def wtc_term (q h : ℕ) : ℝ :=
    (3 * h : ℝ) * (q.choose h : ℝ) * ((3 * q / 2).choose (3 * h / 2) : ℝ) /
      ((3 * q).choose (3 * h) : ℝ) * (21 / 20 : ℝ) ^ (3 * h)

noncomputable def wtc_mass (q : ℕ) : ℝ :=
    ∑ h ∈ Finset.range (q + 1), if 1 ≤ h ∧ h ≤ q / 2 then wtc_term q h else 0


set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

lemma wtc_choose_lower_two (q h : ℕ) (h2 : 2 ≤ h) (hh : 2 * h ≤ q) :
    q * (q - 1) * 2 ^ (h - 2) ≤ h * (h - 1) * q.choose h := by
  have hi := wtc_choose_lower (q - 1) (h - 1) (by omega) (by omega)
  have he := Nat.add_one_mul_choose_eq (q - 1) (h - 1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ q), Nat.sub_add_cancel (by omega : 1 ≤ h)] at he
  have he' : h - 1 - 1 = h - 2 := by omega
  rw [he'] at hi
  nlinarith only [Nat.mul_le_mul_left q hi, congrArg (fun x => (h - 1) * x) he]

lemma wtc_first_term (q : ℕ) (hq : 3 ≤ q) (hodd : q % 2 = 1) :
    wtc_term q 1 = 3 * (21 / 20 : ℝ)^3 / (3 * (q : ℝ) - 2) := by
  have hmN : 2 * (3 * q / 2) = 3 * q - 1 := by omega
  have hmR : 2 * ((3 * q / 2 : ℕ) : ℝ) = 3 * (q : ℝ) - 1 := by
    have ht : 2 * ((3 * q / 2 : ℕ) : ℝ) + 1 = 3 * (q : ℝ) := by
      exact_mod_cast (show 2 * (3 * q / 2) + 1 = 3 * q by omega)
    linarith
  have he := Nat.descFactorial_eq_factorial_mul_choose (3 * q) 3
  norm_num only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero,
    Nat.factorial_succ, Nat.factorial_zero] at he
  have heR : (3 * (q : ℝ) - 2) * (3 * (q : ℝ) - 1) * (3 * (q : ℝ)) =
      6 * ((3 * q).choose 3 : ℝ) := by
    have ht := congrArg (fun x : ℕ => (x : ℝ)) he
    simp only [Nat.cast_mul, Nat.cast_one] at ht
    rw [Nat.cast_sub (by omega : 2 ≤ 3 * q), Nat.cast_sub (by omega : 1 ≤ 3 * q)] at ht
    push_cast at ht
    nlinarith only [ht]
  have hc : ((3 * q).choose 3 : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero (by omega : 3 ≤ 3 * q)
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  unfold wtc_term
  norm_num only [Nat.choose_one_right, Nat.mul_one, Nat.reduceDiv]
  field_simp [hc, ne_of_gt (by linarith : (0 : ℝ) < 3 * (q : ℝ) - 2)]
  nlinarith only [heR, congrArg (fun x : ℝ => x * (3 * (q : ℝ)) * (3 * (q : ℝ) - 2)) hmR]

lemma wtc_term_bound_sharper (q h : ℕ) (hq : 100001 ≤ q) (hodd : q % 2 = 1)
    (h1 : 1 ≤ h) (hh : 2 * h ≤ q) :
    wtc_term q h ≤ (3 / 50000 : ℝ) * (h : ℝ)^2 * (5 / 6 : ℝ)^h := by
  by_cases heq : h = 1
  · subst h
    rw [wtc_first_term q (by omega) hodd]
    norm_num
    have hqR : (100001 : ℝ) ≤ q := by exact_mod_cast hq
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 3 * (q : ℝ) - 2)]
    linarith
  have h2 : 2 ≤ h := by omega
  let B : ℝ := q.choose h
  let C : ℝ := (3 * q).choose (3 * h)
  let D : ℝ := (3 * q / 2).choose (3 * h / 2)
  have hb : 0 < B := by dsimp only [B]; exact_mod_cast Nat.choose_pos (by omega : h ≤ q)
  have hc : 0 < C := by dsimp only [C]; exact_mod_cast Nat.choose_pos (by omega : 3 * h ≤ 3 * q)
  have hd : 0 ≤ D := by positivity
  have hb3 : B^3 ≤ C := by dsimp only [B, C]; exact_mod_cast wtc_choose_cube q h
  have hn : 2 * (3 * q / 2) + 1 = 3 * q := by omega
  have hd2 : D^2 ≤ C := by
    dsimp only [D, C]
    exact_mod_cast (hn ▸ wtc_choose_square (3 * q / 2) (3 * h))
  have hchoose : (q : ℝ) * ((q : ℝ) - 1) * 2^(h-2) ≤ (h : ℝ) * ((h : ℝ) - 1) * B := by
    dsimp only [B]
    have ht : ((q * (q - 1) * 2 ^ (h - 2) : ℕ) : ℝ) ≤
        ((h * (h - 1) * q.choose h : ℕ) : ℝ) := by exact_mod_cast wtc_choose_lower_two q h h2 hh
    simp only [Nat.cast_mul] at ht
    rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_sub (by omega : 1 ≤ h)] at ht
    simpa using ht
  have hqR : (100001 : ℝ) ≤ q := by exact_mod_cast hq
  have hhR : 2 ≤ (h : ℝ) := by exact_mod_cast h2
  have hhm : 0 ≤ (h : ℝ) - 1 := by linarith
  have hqm : 0 < (q : ℝ) - 1 := by linarith
  have hbase : (21 / 20 : ℝ)^6 ≤ 2 * (5 / 6 : ℝ)^2 := by norm_num
  have hpw := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (21 / 20)^6) hbase h
  have hpweq : ((21 / 20 : ℝ) ^ (3 * h))^2 ≤ 2^h * ((5 / 6 : ℝ)^h)^2 := by
    have he1 : 3 * h * 2 = 6 * h := by omega
    have he2 : 2 * h = h * 2 := by omega
    simpa only [mul_pow, ← pow_mul, he1, he2] using hpw
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
    calc _ ≤ ((h : ℝ) * ((h : ℝ)-1) * B) * (B * D / C)^2 :=
          mul_le_mul_of_nonneg_right hchoose (sq_nonneg _)
      _ = (h : ℝ) * ((h : ℝ)-1) * (B * (B * D / C)^2) := by ring
      _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ (h : ℝ)*((h : ℝ)-1))
  have hs := mul_le_mul hratio' hpweq (by positivity) (by positivity : 0 ≤ (h : ℝ)*((h : ℝ)-1))
  rw [h2pow] at hs
  have hs' : (q : ℝ) * ((q : ℝ)-1) * (B * D / C)^2 * ((21 / 20 : ℝ) ^ (3*h))^2 ≤
      4 * (h : ℝ) * ((h : ℝ)-1) * ((5/6 : ℝ)^h)^2 := by
    apply (mul_le_mul_iff_of_pos_left (by positivity : (0 : ℝ) < 2^(h-2))).mp
    nlinarith only [hs]
  have hquot : (wtc_term q h)^2 =
      9 * (h : ℝ)^2 * (B * D / C)^2 * ((21 / 20 : ℝ)^(3*h))^2 := by
    dsimp [wtc_term, B, C, D]; push_cast; ring
  have hupper : (q : ℝ) * ((q : ℝ)-1) * (wtc_term q h)^2 ≤ 36 * (h : ℝ)^4 * ((5/6 : ℝ)^h)^2 := by
    rw [hquot]
    have hmul := mul_le_mul_of_nonneg_left hs' (by positivity : 0 ≤ 9*(h : ℝ)^2)
    have hhh : (h : ℝ) * ((h : ℝ)-1) ≤ (h : ℝ)^2 := by nlinarith
    have hmul2 := mul_le_mul_of_nonneg_left hhh (by positivity : 0 ≤ 36*(h : ℝ)^2*((5/6 : ℝ)^h)^2)
    nlinarith only [hmul, hmul2]
  have hqq : (10000000000 : ℝ) ≤ (q : ℝ) * ((q : ℝ)-1) := by nlinarith [sq_nonneg ((q : ℝ)-100001)]
  have hsq : (wtc_term q h)^2 ≤ ((3 / 50000 : ℝ) * (h : ℝ)^2 * (5 / 6 : ℝ)^h)^2 := by
    apply (mul_le_mul_iff_of_pos_left (by positivity : (0 : ℝ) < (q : ℝ)*((q : ℝ)-1))).mp
    calc _ ≤ 36 * (h : ℝ)^4 * ((5/6 : ℝ)^h)^2 := hupper
      _ ≤ _ := by
        have hx := mul_le_mul_of_nonneg_right hqq (by positivity :
          0 ≤ ((3 / 50000 : ℝ) * (h : ℝ)^2 * (5 / 6 : ℝ)^h)^2)
        nlinarith only [hx]
  have hnon : 0 ≤ (3 / 50000 : ℝ) * (h : ℝ)^2 * (5 / 6 : ℝ)^h := by positivity
  nlinarith [sq_nonneg (wtc_term q h + (3 / 50000 : ℝ) * (h : ℝ)^2 * (5 / 6 : ℝ)^h)]

lemma wtc_mass_bound_sharper (q : ℕ) (hq : 100001 ≤ q) (hodd : q % 2 = 1) :
    wtc_mass q ≤ 1 / 50 := by
  have hs : wtc_mass q ≤ (3 / 50000 : ℝ) *
      ∑ h ∈ Finset.range (q + 1), (h : ℝ)^2 * (5 / 6 : ℝ)^h := by
    unfold wtc_mass
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun h hh => ?_
    split_ifs with hcond
    · simpa only [mul_assoc] using wtc_term_bound_sharper q h hq hodd hcond.1 (by omega)
    · positivity
  have hg := wtc_geometric_square_sum (q + 1)
  nlinarith
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

lemma wtc_factorial_weight (q d : ℕ) :
    (d.factorial : ℝ) * wtc_wt (q := q) d =
      (21 / 20 : ℝ)^d / ((3 * q).choose d : ℝ) := by
  unfold wtc_wt
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  have hf : (d.factorial : ℝ) ≠ 0 := by positivity
  by_cases hc : ((3 * q).choose d : ℝ) = 0
  · simp [hc]
  · field_simp


lemma wtc_position_identity (q h : ℕ) (hq : 1 ≤ q) (h1 : 1 ≤ h) :
    ((q - 1).choose (h - 1) : ℝ) * (3 * q : ℝ) *
      (((3 * h).factorial * (3 * q / 2).choose (3 * h / 2) : ℕ) : ℝ) *
      wtc_wt (q := q) (3 * h) = wtc_term q h := by
  have hi := Nat.add_one_mul_choose_eq (q - 1) (h - 1)
  rw [Nat.sub_add_cancel hq, Nat.sub_add_cancel h1] at hi
  have hir : (q : ℝ) * ((q - 1).choose (h - 1) : ℝ) = (q.choose h : ℝ) * (h : ℝ) := by
    exact_mod_cast hi
  push_cast
  calc _ = 3 * ((q : ℝ) * ((q - 1).choose (h - 1) : ℝ)) *
      ((3 * q / 2).choose (3 * h / 2) : ℝ) *
      (( (3 * h).factorial : ℝ) * wtc_wt (q := q) (3 * h)) := by ring
    _ = _ := by rw [hir, wtc_factorial_weight]; unfold wtc_term; push_cast; ring

lemma wtc_vertex_coefficient (n s : ℕ) (hodd : n % 2 = 1) (hn : 3 ≤ n) (hs : 3 ≤ s) :
    (if s % 2 = 1 then (n / 2).choose (s / 2) else 0) +
      (n - 1) * (n / 2 - 1).choose (s / 2 - 1) = s * (n / 2).choose (s / 2) := by
  have hi := Nat.add_one_mul_choose_eq (n / 2 - 1) (s / 2 - 1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n / 2), Nat.sub_add_cancel (by omega : 1 ≤ s / 2)] at hi
  have hn' : n - 1 = 2 * (n / 2) := by omega
  rw [hn']
  split_ifs with hmod
  · have hs' : s = 2 * (s / 2) + 1 := by omega
    nlinarith only [hi, congrArg (fun x => x * (n / 2).choose (s / 2)) hs']
  · have hs' : s = 2 * (s / 2) := by omega
    nlinarith only [hi, congrArg (fun x => x * (n / 2).choose (s / 2)) hs']

lemma wtc_position_sum_eq (q : ℕ) (hq : 1 ≤ q) :
    (∑ m ∈ Finset.range q, ((q - 1).choose m : ℝ) *
      (if m + 1 ≤ q / 2 then (3 * q : ℝ) *
        (((3 * (m + 1)).factorial * (3 * q / 2).choose (3 * (m + 1) / 2) : ℕ) : ℝ) *
        wtc_wt (q := q) (3 * (m + 1)) else 0)) = wtc_mass q := by
  unfold wtc_mass
  rw [Finset.sum_range_succ']
  simp only [not_le.mpr (by omega : 0 < 1), false_and, if_false, add_zero]
  refine Finset.sum_congr rfl fun m hm => ?_
  by_cases hb : m + 1 ≤ q / 2
  · simp only [hb, if_true, Nat.add_sub_cancel, show 1 ≤ m + 1 by omega, true_and]
    simpa only [Nat.add_sub_cancel, mul_assoc] using wtc_position_identity q (m + 1) hq (by omega)
  · simp only [hb, if_false, and_false, mul_zero]

lemma wtc_vertex_sum_eq (q : ℕ) (hq : 1 ≤ q) (hodd : q % 2 = 1) :
    (∑ m ∈ Finset.range (q + 1), (q.choose m : ℝ) *
      (if 1 ≤ m ∧ m ≤ q / 2 then
        ((((3 * m).factorial * (if (3 * m) % 2 = 1 then (3 * q / 2).choose (3 * m / 2) else 0)
        + (3 * q - 1) * ((3 * m).factorial * (3 * q / 2 - 1).choose (3 * m / 2 - 1)) : ℕ) : ℝ)) *
        wtc_wt (q := q) (3 * m) else 0)) = wtc_mass q := by
  unfold wtc_mass
  refine Finset.sum_congr rfl fun h hh => ?_
  by_cases hcond : 1 ≤ h ∧ h ≤ q / 2
  · simp only [if_pos hcond]
    have hn : (3 * q) % 2 = 1 := by omega
    have hi := wtc_vertex_coefficient (3 * q) (3 * h) hn (by omega) (by omega)
    have hi' : (3 * h).factorial * (if (3 * h) % 2 = 1 then (3 * q / 2).choose (3 * h / 2) else 0)
        + (3 * q - 1) * ((3 * h).factorial * (3 * q / 2 - 1).choose (3 * h / 2 - 1)) =
        (3 * h).factorial * (3 * h * (3 * q / 2).choose (3 * h / 2)) := by nlinarith [hi]
    rw [hi']
    push_cast
    calc _ = (3 * (h : ℝ)) * (q.choose h : ℝ) * ((3 * q / 2).choose (3 * h / 2) : ℝ) *
        (((3 * h).factorial : ℝ) * wtc_wt (q := q) (3 * h)) := by ring
      _ = _ := by rw [wtc_factorial_weight]; unfold wtc_term; push_cast; ring
  · simp only [if_neg hcond, mul_zero]

theorem wild_triple_partition_large_order_mass_bound (q : ℕ) (hq : 100001 ≤ q) (hodd : q % 2 = 1) :
    (∑ m ∈ Finset.range q, ((Nat.choose (q - 1) m : ℕ) : ℝ) *
      (if m + 1 ≤ q / 2 then (3 * q : ℝ) * (((3 * (m + 1)).factorial * Nat.choose (3 * q / 2) (3 * (m + 1) / 2) : ℕ) : ℝ) *
        wtc_wt (q := q) (3 * (m + 1)) else 0) ≤ 1 / 50) ∧ (∑ m ∈ Finset.range (q + 1), ((Nat.choose q m : ℕ) : ℝ) *
      (if 1 ≤ m ∧ m ≤ q / 2 then ((((3 * m).factorial * (if (3 * m) % 2 = 1 then Nat.choose (3 * q / 2) (3 * m / 2) else 0)
        + (3 * q - 1) * ((3 * m).factorial * Nat.choose (3 * q / 2 - 1) (3 * m / 2 - 1)) : ℕ) : ℝ)) *
        wtc_wt (q := q) (3 * m) else 0) ≤ 1 / 50) := by
  have hmass := wtc_mass_bound_sharper q hq hodd
  exact ⟨(wtc_position_sum_eq q (by omega)).trans_le hmass, (wtc_vertex_sum_eq q (by omega) hodd).trans_le hmass⟩
