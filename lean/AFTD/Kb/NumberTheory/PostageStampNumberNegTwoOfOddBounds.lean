import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.NumberTheory.PostageStampNumberNegTwoOfOddSumRepr
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.NumberTheory.IntMemHFoldSumset

/-!
# postage_stamp_number_neg_two_of_odd_bounds

Topic: elementary_number_theory   Node: f0dbca168871

Provenance: helper lemma. arXiv:2610.19470 (Positivity and negativity for h-bases for N), Theorem 4.1 and its proof

If {a, a+x, a+y} (a < 0 < x < y) h-fold covers [0, R] with h = 2m+1 and R ≥ 2m+2, then x, y are coprime and (y-1)(1-x) ≥ ha ≥ R - (2m+2)y + 1 + (y-1)(y-x) (the inequalities of the proof of Theorem 4.1 of arXiv:2610.19470, at any range R).
-/

theorem postage_stamp_number_neg_two_of_odd_bounds
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
      postage_stamp_number_neg_two_of_odd_sum_repr (2*m+1) a x y hx0 hy0 hxy0 f hf
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
