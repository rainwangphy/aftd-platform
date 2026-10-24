import AFTD.Prelude
import AFTD.Kb.NumberTheory.PostageStampBasisRange
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.NumberTheory.IntMemHFoldSumset
import AFTD.Kb.NumberTheory.PostageStampNumberNeg
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# postage_stamp_number_neg_four_one_nine_two_add_six_le

Topic: elementary_number_theory   Node: 9114229df286

Provenance: original. Related work: arXiv:2610.19470 (Positivity and negativity for h-bases for N), Theorem 4.1 (n♭_h(2) < n_h(2) for odd h)

For h = 419 (h ≡ 59 mod 60), the negative-allowed three-stamp number satisfies n♭_h(2) ≤ n_h(2) - 6, where n_h(2) = ⌊(h²+6h+1)/4⌋ = 44519. This refutes the conjectured value n♭_h(2) = n_h(2) - 4 for h ≡ 59 (mod 60) (postage_stamp_number_neg_two_of_odd).
-/

lemma postage_stamp_number_neg_four_one_nine_sum_repr
    (h : ℕ) (a x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y)
    (f : Fin h → ℤ) (hf : ∀ i, f i ∈ ({a, a + x, a + y} : Finset ℤ)) :
    ∃ s t : ℕ, s + t ≤ h ∧ ∑ i, f i = h * a + s * x + t * y := by
  refine ⟨(Finset.univ.filter (fun i : Fin h => f i = a + x)).card,
          (Finset.univ.filter (fun i : Fin h => f i = a + y)).card, ?_, ?_⟩
  · have hdisj : Disjoint (Finset.univ.filter (fun i : Fin h => f i = a + x))
        (Finset.univ.filter (fun i : Fin h => f i = a + y)) := by
      rw [Finset.disjoint_left]
      intro i hi1 hi2
      simp only [Finset.mem_filter] at hi1 hi2
      omega
    calc (Finset.univ.filter (fun i : Fin h => f i = a + x)).card +
        (Finset.univ.filter (fun i : Fin h => f i = a + y)).card
        = (Finset.univ.filter (fun i : Fin h => f i = a + x) ∪
           Finset.univ.filter (fun i : Fin h => f i = a + y)).card := (Finset.card_union_of_disjoint hdisj).symm
      _ ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ _)
      _ = h := by simp
  · have hpt : ∀ i : Fin h, f i = a + (if f i = a + x then x else 0) + (if f i = a + y then y else 0) := by
      intro i
      have hmem := hf i
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      have hax : ¬ (a = a + x) := by omega
      have hay : ¬ (a = a + y) := by omega
      have hxy' : ¬ (a + x = a + y) := by omega
      have hyx' : ¬ (a + y = a + x) := by omega
      rcases hmem with h1 | h1 | h1
      · subst h1; simp [hax, hay]
      · rw [h1]; simp [hxy']
      · rw [h1]; simp [hyx']
    rw [Finset.sum_congr rfl (fun i _ => hpt i)]
    simp only [Finset.sum_add_distrib]
    have h1 : (∑ i : Fin h, a) = h * a := by simp [Finset.sum_const]
    have h2 : (∑ i : Fin h, (if f i = a + x then x else 0)) =
        (Finset.univ.filter (fun i : Fin h => f i = a + x)).card * x := by
      rw [← Finset.sum_filter]; simp [Finset.sum_const]
    have h3 : (∑ i : Fin h, (if f i = a + y then y else 0)) =
        (Finset.univ.filter (fun i : Fin h => f i = a + y)).card * y := by
      rw [← Finset.sum_filter]; simp [Finset.sum_const]
    rw [h1, h2, h3]

lemma postage_stamp_number_neg_four_one_nine_bounds
    (m R : ℕ) (hR : 2*m+1+1 ≤ R) (a x y : ℤ) (hx : 0 < x) (hxy : x < y) (ha : a < 0)
    (hsub : ∀ n : ℕ, n ≤ R →
      int_mem_h_fold_sumset (2*m+1) {a, a+x, a+y} n) :
    IsCoprime x y ∧ (2*(m:ℤ)+1)*a ≤ (y-1)*(1-x) ∧
      ((R : ℕ) : ℤ) - (2*(m:ℤ)+2)*y + 1 + (y-1)*(y-x) ≤ (2*(m:ℤ)+1)*a := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hxy0 : x ≠ y := ne_of_lt hxy
  have hy0 : y ≠ 0 := by omega
  have hypos : 0 < y := by linarith
  have hNge : 2*m+1+1 ≤ R := hR
  have hrepr : ∀ n : ℕ, n ≤ R → ∃ s t : ℕ, s + t ≤ 2*m+1 ∧ (n:ℤ) = (2*(m:ℤ)+1)*a + s*x + t*y := by
    intro n hn
    have hmem := hsub n hn
    simp only [int_mem_h_fold_sumset] at hmem
    obtain ⟨f, hf, hsum⟩ := hmem
    obtain ⟨s, t, hst, hrep⟩ :=
      postage_stamp_number_neg_four_one_nine_sum_repr (2*m+1) a x y hx0 hy0 hxy0 f hf
    refine ⟨s, t, hst, ?_⟩
    rw [← hsum, hrep]
    push_cast
    ring
  have hcop : IsCoprime x y := by
    have hdvd_all : ∀ n : ℕ, n ≤ R → ((Int.gcd x y : ℕ) : ℤ) ∣ (n:ℤ) - (2*(m:ℤ)+1)*a := by
      intro n hn
      obtain ⟨s, t, hst, hreprn⟩ := hrepr n hn
      have h1 : ((Int.gcd x y : ℕ) : ℤ) ∣ (s:ℤ)*x :=
        dvd_mul_of_dvd_right (Int.gcd_dvd_left x y) _
      have h2 : ((Int.gcd x y : ℕ) : ℤ) ∣ (t:ℤ)*y :=
        dvd_mul_of_dvd_right (Int.gcd_dvd_right x y) _
      have hcast : (n:ℤ) - (2*(m:ℤ)+1)*a = (s:ℤ)*x + (t:ℤ)*y := by rw [hreprn]; ring
      rw [hcast]; exact dvd_add h1 h2
    have hgcd1 : Int.gcd x y = 1 := by
      have h0 := hdvd_all 0 (by omega)
      have h1 := hdvd_all 1 (by omega)
      simp only [Nat.cast_zero, Nat.cast_one] at h0 h1
      have hsub1 : ((Int.gcd x y : ℕ) : ℤ) ∣ (1:ℤ) := by
        have := Int.dvd_sub h1 h0
        simpa using this
      have hle : (Int.gcd x y : ℤ) ≤ 1 := Int.le_of_dvd (by norm_num) hsub1
      have hpos : (0:ℤ) ≤ (Int.gcd x y : ℤ) := Nat.cast_nonneg _
      have hne : Int.gcd x y ≠ 0 := by
        intro h; rw [h] at hsub1; simp at hsub1
      omega
    exact Int.isCoprime_iff_gcd_eq_one.mpr hgcd1
  have hyh : y ≤ 2*(m:ℤ)+1+1 := by
    by_contra hcon
    push Not at hcon
    classical
    have hex : ∀ n : ℕ, n ≤ 2*m+1+1 → ∃ s t : ℕ, s+t ≤ 2*m+1 ∧ (n:ℤ) = (2*(m:ℤ)+1)*a + s*x + t*y :=
      fun n hn => hrepr n (le_trans hn hNge)
    let S : ℕ → ℕ := fun n => if hn : n ≤ 2*m+1+1 then (hex n hn).choose else 0
    have hS : ∀ n (hn : n ≤ 2*m+1+1), ∃ t, S n + t ≤ 2*m+1 ∧ (n:ℤ) = (2*(m:ℤ)+1)*a + S n*x + t*y := by
      intro n hn
      simp only [S, dif_pos hn]
      exact (hex n hn).choose_spec
    have hSinj : ∀ n n' (hn : n ≤ 2*m+1+1) (hn' : n' ≤ 2*m+1+1), S n = S n' → n = n' := by
      intro n n' hn hn' heq
      obtain ⟨t, ht, hrepn⟩ := hS n hn
      obtain ⟨t', ht', hrepn'⟩ := hS n' hn'
      rw [heq] at hrepn
      have hdvd : y ∣ (n:ℤ) - (n':ℤ) := by
        refine ⟨(t:ℤ) - t', ?_⟩
        rw [hrepn, hrepn']; ring
      have hlt : |(n:ℤ) - (n':ℤ)| < y := by
        have h1 : (0:ℤ) ≤ (n:ℤ) := Nat.cast_nonneg n
        have h2 : (n:ℤ) ≤ 2*(m:ℤ)+1+1 := by exact_mod_cast hn
        have h3 : (0:ℤ) ≤ (n':ℤ) := Nat.cast_nonneg n'
        have h4 : (n':ℤ) ≤ 2*(m:ℤ)+1+1 := by exact_mod_cast hn'
        rw [abs_lt]; constructor <;> linarith
      have hzero := Int.eq_zero_of_abs_lt_dvd hdvd hlt
      have : (n:ℤ) = (n':ℤ) := by linarith
      exact_mod_cast this
    have himg : (Finset.range (2*m+1+1+1)).image S ⊆ Finset.range (2*m+1+1) := by
      intro z hz
      simp only [Finset.mem_image, Finset.mem_range] at hz
      obtain ⟨n, hn, rfl⟩ := hz
      obtain ⟨t, ht, _⟩ := hS n (by omega)
      exact Finset.mem_range.mpr (by omega)
    have hcard : (Finset.range (2*m+1+1+1)).card ≤ (Finset.range (2*m+1+1)).card := by
      calc (Finset.range (2*m+1+1+1)).card = ((Finset.range (2*m+1+1+1)).image S).card := by
              rw [Finset.card_image_of_injOn]
              intro n hn n' hn' heq
              simp only [Finset.mem_coe, Finset.mem_range] at hn hn'
              exact hSinj n n' (by omega) (by omega) heq
        _ ≤ _ := Finset.card_le_card himg
    simp only [Finset.card_range] at hcard
    omega
  set M : ℤ := ((R : ℕ) : ℤ) with hMdef
  have hNgeZ : 2*(m:ℤ)+2 ≤ M := by
    rw [hMdef]
    have h2 : ((2*m+1+1 : ℕ) : ℤ) ≤ ((R : ℕ) : ℤ) := by exact_mod_cast hNge
    have h3 : ((2*m+1+1 : ℕ) : ℤ) = 2*(m:ℤ)+2 := by push_cast; ring
    linarith
  obtain ⟨r3, hr3a, hr3b, hr3c⟩ : ∃ r3 : ℤ, 0 ≤ r3 ∧ r3 < y ∧
      y ∣ r3 - ((2*(m:ℤ)+1)*a - x) := by
    refine ⟨((2*(m:ℤ)+1)*a - x) % y, Int.emod_nonneg _ (ne_of_gt hypos),
      Int.emod_lt_of_pos _ hypos, ?_⟩
    refine ⟨-(((2*(m:ℤ)+1)*a - x) / y), ?_⟩
    rw [Int.emod_def]; ring
  set n3 : ℕ := r3.toNat with hn3def
  have hn3val : (n3:ℤ) = r3 := Int.toNat_of_nonneg hr3a
  have hn3N : n3 ≤ R := by
    have h1 : (n3:ℤ) ≤ M := by rw [hn3val]; linarith
    rw [hMdef] at h1
    exact_mod_cast h1
  obtain ⟨s3, t3, hst3, hrepr3⟩ := hrepr n3 hn3N
  have hr3eq : r3 = (2*(m:ℤ)+1)*a + s3*x + t3*y := by rw [← hn3val]; exact hrepr3
  have hxs3 : y ∣ ((s3:ℤ)+1)*x := by
    have hy_t : y ∣ (t3:ℤ)*y := ⟨(t3:ℤ), by ring⟩
    have hsum : r3 - ((2*(m:ℤ)+1)*a - x) = ((s3:ℤ)+1)*x + (t3:ℤ)*y := by rw [hr3eq]; ring
    have hmain : y ∣ ((s3:ℤ)+1)*x + (t3:ℤ)*y := by rw [← hsum]; exact hr3c
    have h := Int.dvd_sub hmain hy_t
    simpa using h
  have hy_dvd_s3 : y ∣ ((s3:ℤ)+1) := by
    have h1 : y ∣ x * ((s3:ℤ)+1) := by rw [mul_comm]; exact hxs3
    exact hcop.symm.dvd_of_dvd_mul_left h1
  have hs3ge : (y:ℤ) ≤ (s3:ℤ)+1 := by
    refine Int.le_of_dvd ?_ hy_dvd_s3
    have : (0:ℤ) ≤ (s3:ℤ) := Nat.cast_nonneg s3
    linarith
  have haU : (2*(m:ℤ)+1)*a ≤ (y-1)*(1-x) := by
    have h1 : (2*(m:ℤ)+1)*a + (y-1)*x ≤ (n3:ℤ) := by
      rw [hrepr3]
      have hxle : (0:ℤ) ≤ ((s3:ℤ) - (y-1)) * x :=
        mul_nonneg (by linarith) (le_of_lt hx)
      have ht3 : (0:ℤ) ≤ (t3:ℤ) * y := mul_nonneg (Nat.cast_nonneg t3) (le_of_lt hypos)
      nlinarith
    have h2 : (n3:ℤ) ≤ y - 1 := by rw [hn3val]; linarith
    nlinarith
  obtain ⟨r4, hr4a, hr4b, hr4c⟩ : ∃ r4 : ℤ, M - y + 1 ≤ r4 ∧ r4 ≤ M ∧
      y ∣ r4 - ((2*(m:ℤ)+1)*a - x) := by
    refine ⟨M - y + 1 + (((2*(m:ℤ)+1)*a - x) - (M - y + 1)) % y, ?_, ?_, ?_⟩
    · have := Int.emod_nonneg (((2*(m:ℤ)+1)*a - x) - (M - y + 1)) (ne_of_gt hypos)
      linarith
    · have := Int.emod_lt_of_pos (((2*(m:ℤ)+1)*a - x) - (M - y + 1)) hypos
      linarith
    · refine ⟨-((((2*(m:ℤ)+1)*a - x) - (M - y + 1)) / y), ?_⟩
      rw [Int.emod_def]; ring
  set n4 : ℕ := r4.toNat with hn4def
  have hn4val : (n4:ℤ) = r4 := Int.toNat_of_nonneg (by linarith [hr4a, hNgeZ])
  have hn4N : n4 ≤ R := by
    have h1 : (n4:ℤ) ≤ M := by rw [hn4val]; exact hr4b
    rw [hMdef] at h1
    exact_mod_cast h1
  obtain ⟨s4, t4, hst4, hrepr4⟩ := hrepr n4 hn4N
  have hr4eq : r4 = (2*(m:ℤ)+1)*a + s4*x + t4*y := by rw [← hn4val]; exact hrepr4
  have hxs4 : y ∣ ((s4:ℤ)+1)*x := by
    have hy_t : y ∣ (t4:ℤ)*y := ⟨(t4:ℤ), by ring⟩
    have hsum : r4 - ((2*(m:ℤ)+1)*a - x) = ((s4:ℤ)+1)*x + (t4:ℤ)*y := by rw [hr4eq]; ring
    have hmain : y ∣ ((s4:ℤ)+1)*x + (t4:ℤ)*y := by rw [← hsum]; exact hr4c
    have h := Int.dvd_sub hmain hy_t
    simpa using h
  have hxs4' : y ∣ ((s4:ℤ)+1) := by
    have h1 : y ∣ x * ((s4:ℤ)+1) := by rw [mul_comm]; exact hxs4
    exact hcop.symm.dvd_of_dvd_mul_left h1
  have hs4ge : (y:ℤ) ≤ (s4:ℤ)+1 := by
    refine Int.le_of_dvd ?_ hxs4'
    have : (0:ℤ) ≤ (s4:ℤ) := Nat.cast_nonneg s4
    linarith
  have haL : M - (2*(m:ℤ)+2)*y + 1 + (y-1)*(y-x) ≤ (2*(m:ℤ)+1)*a := by
    have hs4t4 : (s4:ℤ) + t4 ≤ 2*(m:ℤ)+1 := by exact_mod_cast hst4
    have hkey : (s4:ℤ)*x + (t4:ℤ)*y ≤ (2*(m:ℤ)+1)*y - (y-1)*(y-x) := by
      have ht4 : (t4:ℤ) ≤ 2*(m:ℤ)+1 - s4 := by linarith
      have h2 : (t4:ℤ)*y ≤ (2*(m:ℤ)+1 - s4)*y :=
        mul_le_mul_of_nonneg_right ht4 (le_of_lt hypos)
      have h3 : ((y-1) : ℤ)*(y-x) ≤ (s4:ℤ)*(y-x) :=
        mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      nlinarith
    have hb : M - y + 1 ≤ (2*(m:ℤ)+1)*a + s4*x + t4*y := by rw [← hr4eq]; exact hr4a
    linarith
  exact ⟨hcop, haU, haL⟩

lemma postage_stamp_number_neg_four_one_nine_decomp
    (A : Finset ℤ) (hA : A.card = 3) (hneg : ∃ a ∈ A, a < 0) :
    ∃ a x y : ℤ, 0 < x ∧ x < y ∧ a < 0 ∧ A = {a, a + x, a + y} := by
  have hne : A.Nonempty := by
    obtain ⟨b, hb, _⟩ := hneg; exact ⟨b, hb⟩
  obtain ⟨b0, hb0, hb0neg⟩ := hneg
  set a := A.min' hne with ha_def
  have ha_mem : a ∈ A := Finset.min'_mem A hne
  have ha_le : ∀ z ∈ A, a ≤ z := fun z hz => Finset.min'_le A z hz
  have ha_neg : a < 0 := lt_of_le_of_lt (ha_le b0 hb0) hb0neg
  set B := A.erase a with hB_def
  have hBcard : B.card = 2 := by
    rw [hB_def, Finset.card_erase_of_mem ha_mem, hA]
  have hBne : B.Nonempty := by rw [← Finset.card_pos]; omega
  set b := B.min' hBne with hb_def
  set c := B.max' hBne with hc_def
  have hb_mem : b ∈ B := Finset.min'_mem B hBne
  have hc_mem : c ∈ B := Finset.max'_mem B hBne
  have hb_memA : b ∈ A := (Finset.mem_erase.mp hb_mem).2
  have hc_memA : c ∈ A := (Finset.mem_erase.mp hc_mem).2
  have hb_ne_a : b ≠ a := (Finset.mem_erase.mp hb_mem).1
  have hb_le_c : b ≤ c := Finset.min'_le B c hc_mem
  have hb_ne_c : b ≠ c := by
    intro hbc
    have hsub : B ⊆ {b} := by
      intro z hz
      simp only [Finset.mem_singleton]
      have h1 : b ≤ z := Finset.min'_le B z hz
      have h2 : z ≤ c := Finset.le_max' B z hz
      omega
    have hc2 := Finset.card_le_card hsub
    rw [hBcard] at hc2
    simp at hc2
  have hbc : b < c := lt_of_le_of_ne hb_le_c hb_ne_c
  have hab : a < b := lt_of_le_of_ne (ha_le b hb_memA) hb_ne_a.symm
  refine ⟨a, b - a, c - a, by omega, by omega, ha_neg, ?_⟩
  have hB_eq : B = {b, c} := by
    have hsub : ({b, c} : Finset ℤ) ⊆ B := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hb_mem
      · exact hc_mem
    have hcard : ({b,c} : Finset ℤ).card = 2 := Finset.card_pair hb_ne_c
    have h2 := Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hBcard])
    rw [h2]
  have hAeq : A = {a, b, c} := by
    calc A = insert a B := (Finset.insert_erase ha_mem).symm
      _ = insert a {b, c} := by rw [hB_eq]
      _ = {a, b, c} := rfl
  rw [hAeq]
  have e1 : a + (b - a) = b := by ring
  have e2 : a + (c - a) = c := by ring
  rw [e1, e2]

lemma postage_stamp_number_neg_four_one_nine_range_lt (h R : ℕ) (A : Finset ℤ) (hR : 0 < R)
    (key : ¬ ∀ n : ℕ, n ≤ R → int_mem_h_fold_sumset h A n) :
    postage_stamp_basis_range h A + 1 ≤ R := by
  have : postage_stamp_basis_range h A ≤ R - 1 := by
    rw [postage_stamp_basis_range]
    by_cases hne : {n : ℕ | ∀ k : ℕ, k ≤ n → int_mem_h_fold_sumset h A k}.Nonempty
    · apply csSup_le hne
      intro n hn
      by_contra hcon
      push Not at hcon
      apply key
      intro k hk
      exact hn k (by omega)
    · have hempty : {n : ℕ | ∀ k : ℕ, k ≤ n → int_mem_h_fold_sumset h A k} = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp hne
      rw [hempty]
      simp
  omega

lemma postage_stamp_number_neg_four_one_nine_two_add_six_le_range (A : Finset ℤ) (hA : A.card = 3)
    (hneg : ∃ a ∈ A, a < 0) : postage_stamp_basis_range 419 A + 6 ≤ 44519 := by
  obtain ⟨a, x, y, hx, hxy, ha, hAeq⟩ :=
    postage_stamp_number_neg_four_one_nine_decomp A hA hneg
  have key : ¬ ∀ n : ℕ, n ≤ 44514 → int_mem_h_fold_sumset 419 A n := by
    intro hsub
    rw [hAeq] at hsub
    obtain ⟨hcop, haU, haL⟩ :=
      postage_stamp_number_neg_four_one_nine_bounds 209 44514 (by norm_num) a x y hx hxy ha hsub
    push_cast at haU haL
    have hsq : (y - 211) ^ 2 ≤ 5 := by nlinarith
    have hy1 : 209 ≤ y := by nlinarith
    have hy2 : y ≤ 213 := by nlinarith
    rw [Int.isCoprime_iff_gcd_eq_one] at hcop
    interval_cases y
    · obtain ⟨k, hk0, hk5, hke⟩ : ∃ k : ℤ, 0 ≤ k ∧ k ≤ 5 ∧ 419 * a = 208 * (1 - x) - k :=
        ⟨208 * (1 - x) - 419 * a, by omega, by omega, by ring⟩
      interval_cases k
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
    · obtain ⟨k, hk0, hk5, hke⟩ : ∃ k : ℤ, 0 ≤ k ∧ k ≤ 5 ∧ 419 * a = 209 * (1 - x) - k :=
        ⟨209 * (1 - x) - 419 * a, by omega, by omega, by ring⟩
      interval_cases k
      · omega
      · obtain rfl : x = 3 := by omega
        norm_num at hcop
      · obtain rfl : x = 5 := by omega
        norm_num at hcop
      · obtain rfl : x = 7 := by omega
        norm_num at hcop
      · obtain rfl : x = 9 := by omega
        norm_num at hcop
      · omega
    · obtain ⟨k, hk0, hk5, hke⟩ : ∃ k : ℤ, 0 ≤ k ∧ k ≤ 5 ∧ 419 * a = 210 * (1 - x) - k :=
        ⟨210 * (1 - x) - 419 * a, by omega, by omega, by ring⟩
      interval_cases k
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
    · obtain ⟨k, hk0, hk5, hke⟩ : ∃ k : ℤ, 0 ≤ k ∧ k ≤ 5 ∧ 419 * a = 211 * (1 - x) - k :=
        ⟨211 * (1 - x) - 419 * a, by omega, by omega, by ring⟩
      interval_cases k
      · omega
      · obtain rfl : x = 140 := by omega
        norm_num at hcop
      · omega
      · omega
      · obtain rfl : x = 138 := by omega
        norm_num at hcop
      · omega
    · obtain ⟨k, hk0, hk5, hke⟩ : ∃ k : ℤ, 0 ≤ k ∧ k ≤ 5 ∧ 419 * a = 212 * (1 - x) - k :=
        ⟨212 * (1 - x) - 419 * a, by omega, by omega, by ring⟩
      interval_cases k
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega

  have := postage_stamp_number_neg_four_one_nine_range_lt 419 44514 A (by norm_num) key
  omega

theorem postage_stamp_number_neg_four_one_nine_two_add_six_le :
    postage_stamp_number_neg 419 2 + 6 ≤ (419 ^ 2 + 6 * 419 + 1) / 4 := by
  have hne : {n | ∃ A : Finset ℤ, A.card = 2 + 1 ∧ (∃ a ∈ A, a < 0) ∧
      postage_stamp_basis_range 419 A = n}.Nonempty :=
    ⟨_, {-1, 0, 1}, by rfl, ⟨-1, by simp, by norm_num⟩, rfl⟩
  have := csSup_le hne (fun n hn => show n ≤ 44513 by
    obtain ⟨A, hA, hneg, rfl⟩ := hn
    have := postage_stamp_number_neg_four_one_nine_two_add_six_le_range A hA hneg
    omega)
  have h44 : (419 ^ 2 + 6 * 419 + 1) / 4 = 44519 := by norm_num
  rw [h44]
  unfold postage_stamp_number_neg
  omega
