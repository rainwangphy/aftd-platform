import AFTD.Prelude
import AFTD.Kb.NumberTheory.IntMemHFoldSumset
import AFTD.Kb.NumberTheory.PostageStampBasisRange
import AFTD.Kb.NumberTheory.PostageStampNumber
import AFTD.Kb.NumberTheory.PostageStampNumberNeg
import AFTD.Kb.NumberTheory.PostageStampNumberTwoEq
import AFTD.Kb.NumberTheory.PostageStampBasisRangeGeOfModFourEqTwo
import AFTD.Kb.NumberTheory.PostageStampBasisRangeAddOneLeOfNegOfOdd
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# postage_stamp_number_neg_two_eq_of_mod_four_eq_two

Topic: elementary_number_theory   Node: a9f09af7d32e

Provenance: formalization of a published result. Source: arXiv:2610.19470 (Positivity and negativity for h-bases for n), Theorem 3.3 (with the value of n_h(2) from Theorem 1.1).

If h ≥ 2 and h ≡ 2 (mod 4), then n♭_h(2) = n_h(2) = (h² + 6h)/4.
-/

/-- Key combinatorial bound: if a 3-element basis `{a, a+x, a+y}` with `0 < x < y` covers `[0, N]`
with `h` stamps, then either `N ≤ h` or the sharp inequality `N + 2 ≤ y(h+3-y)` holds. -/
lemma postage_stamp_number_neg_two_eq_of_mod_four_eq_two_core
    (h : ℕ) (a x y : ℤ) (N : ℕ) (hh : 1 ≤ h) (hx : 0 < x) (hxy : x < y) (hN : 1 ≤ N)
    (hsub : ∀ m : ℕ, m ≤ N → int_mem_h_fold_sumset h {a, a + x, a + y} (m : ℤ)) :
    N ≤ h ∨ (N : ℤ) + 2 ≤ y * ((h : ℤ) + 3 - y) := by
  classical
  have hy : (0:ℤ) < y := by linarith
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hy0 : y ≠ 0 := ne_of_gt hy
  have hxy0 : x ≠ y := ne_of_lt hxy
  have key : ∀ m : ℕ, m ≤ N → ∃ s t : ℕ, s + t ≤ h ∧ (m : ℤ) = (h : ℤ) * a + s * x + t * y := by
    intro m hm
    obtain ⟨f, hf, hsum⟩ := hsub m hm
    obtain ⟨s, t, hst, heq⟩ :=
      postage_stamp_basis_range_add_one_le_of_neg_of_odd_sum_repr h a x y hx0 hy0 hxy0 f hf
    exact ⟨s, t, hst, by rw [← heq]; exact hsum.symm⟩
  choose j k hjk using key
  let J : ℕ → ℕ := fun m => if hm : m ≤ N then j m hm else 0
  let K : ℕ → ℕ := fun m => if hm : m ≤ N then k m hm else 0
  have hJ : ∀ m (hm : m ≤ N), J m = j m hm := by intro m hm; simp [J, dif_pos hm]
  have hK : ∀ m (hm : m ≤ N), K m = k m hm := by intro m hm; simp [K, dif_pos hm]
  have hval : ∀ m (hm : m ≤ N), (m : ℤ) = (h : ℤ) * a + (J m : ℤ) * x + (K m : ℤ) * y := by
    intro m hm; rw [hJ m hm, hK m hm]; exact (hjk m hm).2
  have hsum_le : ∀ m (hm : m ≤ N), J m + K m ≤ h := by
    intro m hm; rw [hJ m hm, hK m hm]; exact (hjk m hm).1
  have hF3 : ∀ m (hm : m ≤ N), (m:ℤ) ≤ (h:ℤ)*a + y*(h:ℤ) - (J m : ℤ)*(y - x) := by
    intro m hm
    have h1 := hval m hm
    have h2 := hsum_le m hm
    have h3 : (K m : ℤ) ≤ (h:ℤ) - (J m : ℤ) := by
      have h4 : ((J m + K m : ℕ) : ℤ) ≤ (h:ℤ) := by exact_mod_cast h2
      push_cast at h4 ⊢; linarith
    nlinarith [h1, h3, hy]
  have hF6 : ∀ m (hm : m ≤ N), (h:ℤ)*a ≤ (m:ℤ) - (J m : ℤ)*x := by
    intro m hm
    have h1 := hval m hm
    have h2 : (0:ℤ) ≤ (K m : ℤ) * y := by
      have h3 : (0:ℤ) ≤ (K m : ℤ) := Int.natCast_nonneg _
      nlinarith
    nlinarith [h1, h2, hx]
  have hFjle : ∀ m (hm : m ≤ N), J m ≤ h := by
    intro m hm; have := hsum_le m hm; omega
  have hFmod : ∀ m (hm : m ≤ N), y ∣ ((m:ℤ) - (h:ℤ)*a - (J m : ℤ)*x) := by
    intro m hm
    have h1 := hval m hm
    exact ⟨(K m : ℤ), by linarith⟩
  have heuc : ∃ u v : ℤ, u * x + v * y = 1 := by
    have h0 := hval 0 (by omega)
    have h1 := hval 1 hN
    refine ⟨(J 1 : ℤ) - J 0, (K 1 : ℤ) - K 0, ?_⟩
    push_cast at h0 h1 ⊢; linarith
  obtain ⟨Y, hY⟩ : ∃ Y : ℕ, (Y:ℤ) = y := ⟨y.toNat, Int.toNat_of_nonneg (le_of_lt hy)⟩
  have hYpos : 0 < Y := by
    rcases Nat.eq_zero_or_pos Y with h0 | h0
    · rw [h0] at hY; norm_num at hY; linarith
    · exact h0
  have hperl : ∀ m (hm : m ≤ N) (m' : ℕ) (hm' : m' ≤ N), J m % Y = J m' % Y → y ∣ ((m:ℤ) - (m':ℤ)) := by
    intro m hm m' hm' hmod
    have hd1 : (Y:ℤ) ∣ ((J m : ℤ) - (J m' : ℤ)) := by
      have h1 : (J m : ℤ) % (Y:ℤ) = (J m' : ℤ) % (Y:ℤ) := by
        rw [← Int.natCast_emod, ← Int.natCast_emod, hmod]
      have h2 := Int.emod_eq_emod_iff_emod_sub_eq_zero.mp h1
      rwa [Int.dvd_iff_emod_eq_zero]
    have hd2 : y ∣ ((J m : ℤ) - (J m' : ℤ)) := by rw [← hY]; exact hd1
    have hdx : y ∣ (((J m : ℤ) - (J m' : ℤ)) * x) := Dvd.dvd.mul_right hd2 x
    obtain ⟨c1, hc1⟩ := hFmod m hm
    obtain ⟨c2, hc2⟩ := hFmod m' hm'
    have heq : ((m:ℤ) - (m':ℤ)) = ((J m : ℤ) - (J m' : ℤ)) * x + y * (c1 - c2) := by linarith
    rw [heq]
    exact dvd_add hdx ⟨c1 - c2, by ring⟩
  have hperr : ∀ m (hm : m ≤ N) (m' : ℕ) (hm' : m' ≤ N), y ∣ ((m:ℤ) - (m':ℤ)) → J m % Y = J m' % Y := by
    intro m hm m' hm' hdvd
    have hex : ((J m : ℤ) - (J m' : ℤ)) * x = ((m:ℤ) - (m':ℤ)) - ((m:ℤ) - (h:ℤ)*a - (J m : ℤ)*x) + ((m':ℤ) - (h:ℤ)*a - (J m' : ℤ)*x) := by ring
    have h1 : y ∣ (((J m : ℤ) - (J m' : ℤ)) * x) := by
      rw [hex]
      exact dvd_add (dvd_add hdvd (dvd_neg.mpr (hFmod m hm))) (hFmod m' hm')
    obtain ⟨u, v, huv⟩ := heuc
    have h3 : (Y:ℤ) ∣ ((J m : ℤ) - (J m' : ℤ)) := by
      have h2 : ((J m : ℤ) - (J m' : ℤ)) = u * (((J m : ℤ) - (J m' : ℤ)) * x) + (v * ((J m : ℤ) - (J m' : ℤ))) * y := by
        calc ((J m : ℤ) - (J m' : ℤ)) = ((J m : ℤ) - (J m' : ℤ)) * 1 := by ring
          _ = ((J m : ℤ) - (J m' : ℤ)) * (u * x + v * y) := by rw [huv]
          _ = u * (((J m : ℤ) - (J m' : ℤ)) * x) + (v * ((J m : ℤ) - (J m' : ℤ))) * y := by ring
      rw [h2, hY]
      exact dvd_add (Dvd.dvd.mul_left h1 u) (dvd_mul_left y _)
    have h4 : (J m : ℤ) % (Y:ℤ) = (J m' : ℤ) % (Y:ℤ) := by
      rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
      exact (Int.dvd_iff_emod_eq_zero).mp h3
    have h5 : ((J m % Y : ℕ) : ℤ) = ((J m' % Y : ℕ) : ℤ) := by
      rw [Int.natCast_emod, Int.natCast_emod]; exact h4
    exact_mod_cast h5
  by_cases hcase : Y ≤ N + 1
  · have hinj : ∀ m < Y, ∀ m' < Y, J m % Y = J m' % Y → m = m' := by
      intro m hmY m' hm'Y hmod
      have hm : m ≤ N := by omega
      have hm' : m' ≤ N := by omega
      have hdvd := hperl m hm m' hm' hmod
      have hdvd' : (Y:ℤ) ∣ ((m':ℤ) - (m:ℤ)) := by
        rw [show ((m':ℤ) - (m:ℤ)) = -(((m:ℤ)) - ((m':ℤ))) by ring, hY]
        exact dvd_neg.mpr hdvd
      exact (Nat.modEq_iff_dvd.mpr hdvd').eq_of_lt_of_lt hmY hm'Y
    have himg : (Finset.range Y).image (fun m => J m % Y) = Finset.range Y := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_range.mpr (Nat.mod_lt _ hYpos)
      · have h1 : ((Finset.range Y).image (fun m => J m % Y)).card = Y := by
          rw [Finset.card_image_of_injOn]
          · simp
          · exact fun m hm m' hm' heq => hinj m (Finset.mem_range.mp hm) m' (Finset.mem_range.mp hm') heq
        rw [h1]; simp
    have hmem : Y - 1 ∈ (Finset.range Y).image (fun m => J m % Y) := by
      rw [himg]; exact Finset.mem_range.mpr (by omega)
    obtain ⟨m_s, hm_s_range, hm_s⟩ := Finset.mem_image.mp hmem
    have hm_s_lt : m_s < Y := Finset.mem_range.mp hm_s_range
    have hm_s_le : m_s ≤ N := by omega
    have he : m_s + Y * ((N - m_s) / Y) = N - ((N-m_s) % Y) := by
      have hdm := Nat.div_add_mod (N - m_s) Y
      omega
    have htop_le : m_s + Y * ((N - m_s) / Y) ≤ N := by omega
    have htop_lb : (N:ℤ) - (Y:ℤ) + 1 ≤ ((m_s + Y * ((N - m_s) / Y) : ℕ) : ℤ) := by
      have hlt : (N - m_s) % Y ≤ Y - 1 := by have := Nat.mod_lt (N - m_s) hYpos; omega
      have hle : (N - m_s) % Y ≤ N := by omega
      rw [he, Nat.cast_sub hle]
      push_cast
      omega
    have hdvd_top : y ∣ ((((m_s + Y * ((N - m_s) / Y) : ℕ)) : ℤ) - (m_s:ℤ)) := by
      refine ⟨(((N - m_s) / Y : ℕ) : ℤ), ?_⟩
      push_cast
      rw [hY]; ring
    have htop_mod : J (m_s + Y * ((N - m_s) / Y)) % Y = Y - 1 := by
      rw [← hm_s]
      exact hperr _ htop_le m_s hm_s_le hdvd_top
    have hJtop : (Y:ℤ) - 1 ≤ (J (m_s + Y * ((N - m_s) / Y)) : ℤ) := by
      have h1 : J (m_s + Y * ((N - m_s) / Y)) % Y ≤ J (m_s + Y * ((N - m_s) / Y)) := Nat.mod_le _ _
      omega
    have hJbot : (Y:ℤ) - 1 ≤ (J m_s : ℤ) := by
      have h1 : J m_s % Y ≤ J m_s := Nat.mod_le _ _
      omega
    right
    have h3 := hF3 _ htop_le
    have h4 := hF6 m_s hm_s_le
    have hpos : (0:ℤ) < y - x := by linarith
    have h5 : -((J (m_s + Y * ((N - m_s) / Y)) : ℤ) * (y - x)) ≤ -(((Y:ℤ) - 1) * (y - x)) := by nlinarith [hJtop, hpos]
    have hms : (m_s : ℤ) ≤ (Y:ℤ) - 1 := by omega
    have h6 : (h:ℤ)*a ≤ ((Y:ℤ) - 1) - ((Y:ℤ) - 1)*x := by nlinarith [h4, hJbot, hx, hms]
    rw [hY] at htop_lb h5 h6
    nlinarith [h3, h4, h5, h6, htop_lb, hpos]
  · push Not at hcase
    have hN2 : (N:ℤ) + 2 ≤ (Y:ℤ) := by omega
    by_cases hyh : y ≤ (h:ℤ)
    · left
      have h2 : (Y:ℤ) ≤ (h:ℤ) := by rw [hY]; exact hyh
      have : (N:ℤ) ≤ (h:ℤ) := by linarith
      exact_mod_cast this
    · push Not at hyh
      left
      have hJlt : ∀ m (hm : m ≤ N), J m < Y := by
        intro m hm
        have h1 := hFjle m hm
        have h2 : ((J m : ℕ) : ℤ) ≤ (h:ℤ) := by exact_mod_cast h1
        have h3 : ((J m : ℕ) : ℤ) < (Y:ℤ) := by rw [hY]; linarith
        exact_mod_cast h3
      have hinj2 : ∀ m ≤ N, ∀ m' ≤ N, J m = J m' → m = m' := by
        intro m hm m' hm' heq
        have hdvd : y ∣ ((m:ℤ) - (m':ℤ)) := hperl m hm m' hm' (by rw [heq])
        have hdvd' : (Y:ℤ) ∣ ((m':ℤ) - (m:ℤ)) := by
          rw [show ((m':ℤ) - (m:ℤ)) = -(((m:ℤ)) - ((m':ℤ))) by ring, hY]
          exact dvd_neg.mpr hdvd
        have hmY : m < Y := by have := hJlt m hm; omega
        have hmY' : m' < Y := by have := hJlt m' hm'; omega
        exact (Nat.modEq_iff_dvd.mpr hdvd').eq_of_lt_of_lt hmY hmY'
      have hcard : ((Finset.range (N+1)).image J).card = N + 1 := by
        rw [Finset.card_image_of_injOn]
        · simp
        · intro m hm m' hm' heq
          exact hinj2 m (by simpa using hm) m' (by simpa using hm') heq
      have hsub2 : (Finset.range (N+1)).image J ⊆ Finset.range (h+1) := by
        intro x hx
        obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_range.mpr (by have := hFjle m (by simpa using hm); omega)
      have hfin : N + 1 ≤ h + 1 := by
        calc N + 1 = ((Finset.range (N+1)).image J).card := hcard.symm
          _ ≤ (Finset.range (h+1)).card := Finset.card_le_card hsub2
          _ = h + 1 := Finset.card_range _
      omega

/-- Numeric consequence: `N ≤ h` or `N + 2 ≤ y(h+3-y)` forces `N ≤ ⌊(h²+6h+1)/4⌋`. -/
lemma postage_stamp_number_neg_two_eq_of_mod_four_eq_two_num (h N : ℕ) (y : ℤ) (hh : 1 ≤ h)
    (hcase : N ≤ h ∨ (N : ℤ) + 2 ≤ y * ((h : ℤ) + 3 - y)) :
    N ≤ (h ^ 2 + 6 * h + 1) / 4 := by
  rcases hcase with h1 | h1
  · have h2 : 4 * h ≤ h ^ 2 + 6 * h + 1 := by nlinarith
    have h3 : h ≤ (h ^ 2 + 6 * h + 1) / 4 := by
      rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 4)]
      linarith
    omega
  · have h4 : 4 * (y * ((h:ℤ) + 3 - y)) ≤ ((h:ℤ) + 3)^2 := by
      nlinarith [sq_nonneg (2*y - ((h:ℤ)+3))]
    have h5 : 4 * ((N:ℤ) + 2) ≤ ((h:ℤ) + 3)^2 := by linarith
    have h8 : (((h+3)^2 : ℕ) : ℤ) = ((h:ℤ)+3)^2 := by push_cast; ring
    have h9 : (4 * ((N:ℤ) + 2)) ≤ (((h+3)^2 : ℕ) : ℤ) := by rw [h8]; exact h5
    have h7 : ((4 * (N + 2) : ℕ) : ℤ) = 4 * ((N:ℤ)+2) := by push_cast; ring
    have h9' : ((4 * (N + 2) : ℕ) : ℤ) ≤ (((h+3)^2 : ℕ) : ℤ) := by rw [h7]; exact h9
    have h6 : 4 * (N + 2) ≤ (h+3)^2 := by exact_mod_cast h9'
    have h10 : N + 2 ≤ (h+3)^2 / 4 := by
      rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 4)]
      linarith
    have h11 : (h+3)^2 / 4 = (h^2 + 6*h + 1)/4 + 2 := by
      have h12 : (h+3)^2 = (h^2 + 6*h + 1) + 8 := by ring
      rw [h12]
      omega
    omega

/-- Every 3-element set of integers containing a negative element has `h`-range at most
`⌊(h²+6h+1)/4⌋`. -/
lemma postage_stamp_number_neg_two_eq_of_mod_four_eq_two_range_le (h : ℕ) (hh : 1 ≤ h)
    (A : Finset ℤ) (hA : A.card = 3) (hneg : ∃ a ∈ A, a < 0) :
    postage_stamp_basis_range h A ≤ (h ^ 2 + 6 * h + 1) / 4 := by
  rw [postage_stamp_basis_range]
  by_cases hne : ({n : ℕ | ∀ m ≤ n, int_mem_h_fold_sumset h A (m : ℤ)} : Set ℕ).Nonempty
  · refine csSup_le hne ?_
    intro n hn
    by_cases hn1 : n ≤ 1
    · have h2 : (1:ℕ) ≤ (h ^ 2 + 6 * h + 1) / 4 := by
        rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 4)]
        nlinarith
      omega
    · have hn1' : 2 ≤ n := by omega
      obtain ⟨a, x, y, hx, hxy, -, hAeq⟩ :=
        postage_stamp_basis_range_add_one_le_of_neg_of_odd_decomp A hA hneg
      have hsub : ∀ m : ℕ, m ≤ n → int_mem_h_fold_sumset h {a, a + x, a + y} (m : ℤ) := by
        intro m hm
        rw [← hAeq]
        exact hn m hm
      exact postage_stamp_number_neg_two_eq_of_mod_four_eq_two_num h n y hh
        (postage_stamp_number_neg_two_eq_of_mod_four_eq_two_core h a x y n hh hx hxy (by omega) hsub)
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    simp

theorem postage_stamp_number_neg_two_eq_of_mod_four_eq_two (h : ℕ) (hh : 2 ≤ h) (h4 : h % 4 = 2) :
    postage_stamp_number_neg h 2 = (h ^ 2 + 6 * h) / 4 ∧ postage_stamp_number h 2 = (h ^ 2 + 6 * h) / 4 := by
  have hh1 : 1 ≤ h := by omega
  obtain ⟨v, hv⟩ : ∃ v : ℕ, h = 4 * v + 2 := ⟨(h - 2) / 4, by omega⟩
  subst hv
  have harith : ((4*v+2)^2 + 6*(4*v+2) + 1)/4 = ((4*v+2)^2 + 6*(4*v+2))/4 := by
    have e1 : (4*v+2)^2 + 6*(4*v+2) + 1 = 4*(4*v^2 + 10*v + 4) + 1 := by ring
    have e2 : (4*v+2)^2 + 6*(4*v+2) = 4*(4*v^2 + 10*v + 4) := by ring
    rw [e1, e2]; omega
  refine ⟨?_, ?_⟩
  · -- upper and lower bound for n♭
    set S : Set ℕ := {n : ℕ | ∃ A : Finset ℤ, A.card = 2 + 1 ∧ (∃ a ∈ A, a < 0) ∧ postage_stamp_basis_range (4*v+2) A = n} with hS
    have hSdef : postage_stamp_number_neg (4*v+2) 2 = sSup S := by
      rw [postage_stamp_number_neg]
    rw [hSdef]
    refine le_antisymm ?_ ?_
    · by_cases hne : S.Nonempty
      · refine csSup_le hne ?_
        rintro n ⟨A, hAcard, hneg, rfl⟩
        have h1 := postage_stamp_number_neg_two_eq_of_mod_four_eq_two_range_le (4*v+2) (by omega) A hAcard hneg
        rw [← harith]
        exact h1
      · rw [Set.not_nonempty_iff_eq_empty.mp hne]
        simp
    · have hbdd : BddAbove S := by
        refine ⟨((4*v+2)^2 + 6*(4*v+2) + 1) / 4, ?_⟩
        rintro n ⟨A, hAcard, hneg, rfl⟩
        exact postage_stamp_number_neg_two_eq_of_mod_four_eq_two_range_le (4*v+2) (by omega) A hAcard hneg
      have hcardA : ({-(↑(v+1) : ℤ), (↑(v+1) : ℤ), (↑(v+1) : ℤ) + 1} : Finset ℤ).card = 3 := by
        have h1 : (-(↑(v+1) : ℤ)) ∉ ({(↑(v+1) : ℤ), (↑(v+1) : ℤ) + 1} : Finset ℤ) := by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; omega
        have h2 : (↑(v+1) : ℤ) ∉ ({(↑(v+1) : ℤ) + 1} : Finset ℤ) := by
          simp only [Finset.mem_singleton]; omega
        rw [show ({-(↑(v+1) : ℤ), (↑(v+1) : ℤ), (↑(v+1) : ℤ) + 1} : Finset ℤ)
            = insert (-(↑(v+1) : ℤ)) (insert (↑(v+1) : ℤ) ({(↑(v+1) : ℤ) + 1} : Finset ℤ)) from rfl]
        rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2, Finset.card_singleton]
      have hmem : postage_stamp_basis_range (4*v+2) {-(↑(v+1) : ℤ), (↑(v+1) : ℤ), (↑(v+1) : ℤ) + 1} ∈ S := by
        refine ⟨_, hcardA, ?_, rfl⟩
        exact ⟨-(↑(v+1) : ℤ), by simp, by omega⟩
      have hle := le_csSup hbdd hmem
      have heqh : (4*v+2 : ℕ) = 4*(v+1) - 2 := by omega
      rw [heqh] at hle
      have hwit := postage_stamp_basis_range_ge_of_mod_four_eq_two (v+1) (by omega)
      have hval : ((v+1+1) * (4*(v+1) - 2) : ℕ) = ((4*v+2)^2 + 6*(4*v+2))/4 := by
        have h2 : (v+1+1 : ℕ) = v + 2 := by omega
        rw [h2]
        have h3 : 4*(v+1) - 2 = 4*v + 2 := by omega
        rw [h3]
        have e1 : (4*v+2)^2 + 6*(4*v+2) = 4*((v+2)*(4*v+2)) := by ring
        rw [e1]
        exact (Nat.mul_div_cancel_left _ (by norm_num : 0 < 4)).symm
      exact hval ▸ (le_trans hwit hle)
  · -- the classical value n_h(2)
    rw [postage_stamp_number_two_eq (4*v+2) (by omega)]
    exact harith
