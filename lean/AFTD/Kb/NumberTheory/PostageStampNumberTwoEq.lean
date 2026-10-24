import AFTD.Prelude
import AFTD.Kb.NumberTheory.IntMemHFoldSumset
import AFTD.Kb.NumberTheory.PostageStampBasisRange
import AFTD.Kb.NumberTheory.PostageStampNumber
import AFTD.Kb.NumberTheory.PostageStampBasisRangeSuccLeCardPow
import AFTD.Kb.NumberTheory.PostageStampBasisRangeZeroOneGeOfModFourEqZero
import AFTD.Kb.NumberTheory.PostageStampBasisRangeZeroOneGeOfModFourEqTwo
import AFTD.Kb.NumberTheory.PostageStampBasisRangeZeroOneGeOfOdd
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# postage_stamp_number_two_eq

Topic: elementary_number_theory   Node: fb67a9a1d9da

Provenance: formalization of a published result. Source: arXiv:2610.19470 (Positivity and negativity for h-bases for n), Theorem 1.1 (classical; cited there).

The classical postage stamp number for three stamps: n_h(2) = ⌊(h² + 6h + 1)/4⌋ for every h ≥ 1.
-/

lemma postage_stamp_number_two_eq_forward (h : ℕ) (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y)
    (f : Fin h → ℤ) (hf : ∀ i, f i ∈ ({0, x, y} : Finset ℤ)) :
    ∃ i j : ℕ, i + j ≤ h ∧ ∑ k, f k = (i : ℤ) * x + (j : ℤ) * y := by
  classical
  have h0 : ∀ k, f k = 0 ∨ f k = x ∨ f k = y := by
    intro k
    have hk := hf k
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    tauto
  refine ⟨(Finset.univ.filter (fun k => f k = x)).card,
          (Finset.univ.filter (fun k => f k = y)).card, ?_, ?_⟩
  · have hdisj : Disjoint (Finset.univ.filter (fun k => f k = x))
        (Finset.univ.filter (fun k => f k = y)) := by
      rw [Finset.disjoint_left]
      intro a ha hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      rw [ha] at hb
      exact hxy hb
    have hsub : (Finset.univ.filter (fun k => f k = x)) ∪
        (Finset.univ.filter (fun k => f k = y)) ⊆ Finset.univ := by simp
    have h2 := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj] at h2
    simpa using h2
  · have hpt : ∀ k, f k = (if f k = x then x else 0) + (if f k = y then y else 0) := by
      intro k
      rcases h0 k with h' | h' | h'
      · rw [h']; rw [if_neg (fun hh => hx hh.symm), if_neg (fun hh => hy hh.symm)]; ring
      · rw [h']; rw [if_pos rfl, if_neg hxy]; ring
      · rw [h']; rw [if_neg (fun hh => hxy hh.symm), if_pos rfl]; ring
    calc ∑ k, f k
        = ∑ k, ((if f k = x then x else 0) + (if f k = y then y else 0)) :=
          Finset.sum_congr rfl (fun k _ => hpt k)
    _ = ∑ k, (if f k = x then x else 0) + ∑ k, (if f k = y then y else 0) :=
          Finset.sum_add_distrib
    _ = ((Finset.univ.filter (fun k => f k = x)).card : ℤ) * x +
        ((Finset.univ.filter (fun k => f k = y)).card : ℤ) * y := by
        congr 1
        · have hstep : ∑ k, (if f k = x then x else 0) =
              ∑ k, ((if f k = x then (1:ℤ) else 0) * x) := by
            apply Finset.sum_congr rfl
            intro k _
            split <;> simp
          rw [hstep, ← Finset.sum_mul, Finset.sum_boole (fun k => f k = x) Finset.univ]
        · have hstep : ∑ k, (if f k = y then y else 0) =
              ∑ k, ((if f k = y then (1:ℤ) else 0) * y) := by
            apply Finset.sum_congr rfl
            intro k _
            split <;> simp
          rw [hstep, ← Finset.sum_mul, Finset.sum_boole (fun k => f k = y) Finset.univ]

lemma postage_stamp_number_two_eq_arith (h y : ℕ) (hy : 2 ≤ y) (hyh : y ≤ h + 1) :
    (h + 3 - y) * y - 2 ≤ (h^2 + 6*h + 1)/4 := by
  have hkey : 4 * ((h + 3 - y) * y) ≤ (h + 3)^2 := by
    have hz : 4 * ((((h+3-y:ℕ):ℤ) * (y:ℤ))) ≤ ((h:ℤ)+3)^2 := by
      have ht : (((h+3-y:ℕ)):ℤ) + (y:ℤ) = (h:ℤ) + 3 := by
        have : h + 3 - y + y = h + 3 := by omega
        exact_mod_cast this
      nlinarith [sq_nonneg ((((h+3-y:ℕ)):ℤ) - (y:ℤ))]
    exact_mod_cast hz
  have hstep : (h + 3 - y) * y ≤ (h^2 + 6*h + 9)/4 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    calc (h+3-y)*y * 4 = 4 * ((h+3-y)*y) := by ring
    _ ≤ (h+3)^2 := hkey
    _ = h^2 + 6*h + 9 := by ring
  have hX : (h^2 + 6*h + 9)/4 = (h^2+6*h+1)/4 + 2 := by omega
  omega

lemma postage_stamp_number_two_eq_zero_one_bound (h n : ℕ) (hh : 1 ≤ h) (y : ℕ) (hy : 2 ≤ y)
    (hsub : ∀ m : ℕ, m ≤ n → int_mem_h_fold_sumset h ({0, 1, (y:ℤ)} : Finset ℤ) (m:ℤ)) :
    n ≤ (h^2 + 6*h + 1)/4 := by
  have hy0 : (y:ℤ) ≠ 0 := by exact_mod_cast (by omega : y ≠ 0)
  have h1y : (1:ℤ) ≠ (y:ℤ) := by exact_mod_cast (by omega : 1 ≠ y)
  have rep : ∀ m : ℕ, m ≤ n → ∃ i j : ℕ, i + j ≤ h ∧ (m:ℤ) = (i:ℤ) + (j:ℤ)*(y:ℤ) := by
    intro m hm
    obtain ⟨f, hf, hsum⟩ := hsub m hm
    obtain ⟨i, j, hij, he⟩ := postage_stamp_number_two_eq_forward h 1 (y:ℤ) one_ne_zero hy0 h1y f hf
    refine ⟨i, j, hij, ?_⟩
    rw [← hsum, he]
    ring
  have hB : h ≤ (h^2 + 6*h + 1)/4 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    nlinarith
  by_cases hcase : h + 2 ≤ y
  · have hn : n ≤ h := by
      by_contra hcon
      have hhn : h + 1 ≤ n := by omega
      obtain ⟨i, j, hij, he⟩ := rep (h+1) hhn
      have hc : ((h:ℤ)+1) = (i:ℤ) + (j:ℤ)*(y:ℤ) := by exact_mod_cast he
      have hyZ : ((h:ℤ)+2) ≤ (y:ℤ) := by exact_mod_cast hcase
      have hi : (0:ℤ) ≤ (i:ℤ) := by positivity
      have hijZ : (i:ℤ) + (j:ℤ) ≤ (h:ℤ) := by exact_mod_cast hij
      rcases Nat.eq_zero_or_pos j with hj | hj
      · subst hj; simp only [Nat.cast_zero, zero_mul, add_zero] at hc; linarith
      · have hjZ : (1:ℤ) ≤ (j:ℤ) := by exact_mod_cast hj
        nlinarith
    exact le_trans hn hB
  · have hyh : y ≤ h + 1 := by omega
    have hy2 : (2:ℤ) ≤ (y:ℤ) := by exact_mod_cast hy
    have hTY : (((h+3-y:ℕ)):ℤ) + (y:ℤ) = (h:ℤ) + 3 := by
      have : h + 3 - y + y = h + 3 := by omega
      exact_mod_cast this
    have h1ty : 1 ≤ (h+3-y)*y := by
      have h1 : 1 ≤ h + 3 - y := by omega
      have h2 : 1 ≤ y := by omega
      calc 1 = 1*1 := by ring
      _ ≤ (h+3-y)*y := Nat.mul_le_mul h1 h2
    have hn : n ≤ (h+3-y)*y - 2 := by
      by_contra hcon
      have hKn : (h+3-y)*y - 1 ≤ n := by omega
      obtain ⟨i, j, hij, he⟩ := rep ((h+3-y)*y - 1) hKn
      have hKZ : ((((h+3-y)*y - 1 : ℕ)) : ℤ) = (((h+3-y:ℕ)):ℤ) * (y:ℤ) - 1 := by
        rw [Nat.cast_sub h1ty]
        push_cast
        ring
      have hc : (((h+3-y:ℕ)):ℤ) * (y:ℤ) - 1 = (i:ℤ) + (j:ℤ)*(y:ℤ) := by
        rw [← hKZ]; exact_mod_cast he
      have hijZ : (i:ℤ) + (j:ℤ) ≤ (h:ℤ) := by exact_mod_cast hij
      have hi : (0:ℤ) ≤ (i:ℤ) := by positivity
      have hIZ : (i:ℤ) = ((((h+3-y:ℕ)):ℤ) - (j:ℤ)) * (y:ℤ) - 1 := by linarith
      have hk1 : (1:ℤ) ≤ (((h+3-y:ℕ)):ℤ) - (j:ℤ) := by nlinarith
      have hle : (i:ℤ) ≤ ((((h+3-y:ℕ)):ℤ) - (j:ℤ)) + (y:ℤ) - 3 := by linarith
      nlinarith [mul_nonneg (sub_nonneg.2 hk1) (sub_nonneg.2 hy2)]
    calc n ≤ (h+3-y)*y - 2 := hn
    _ ≤ (h^2 + 6*h + 1)/4 := postage_stamp_number_two_eq_arith h y hy hyh

lemma postage_stamp_number_two_eq_pair_bound (h : ℕ) (hh : 1 ≤ h) (p q : ℤ) (hp : 0 < p) (hpq : p < q)
    (n : ℕ) (hn : ∀ m : ℕ, m ≤ n → int_mem_h_fold_sumset h ({0, p, q} : Finset ℤ) (m:ℤ)) :
    n ≤ (h^2+6*h+1)/4 := by
  have hp0 : p ≠ 0 := ne_of_gt hp
  have hq0 : q ≠ 0 := by linarith
  have hpq' : p ≠ q := ne_of_lt hpq
  rcases Nat.eq_zero_or_pos n with hn0 | hn1
  · subst hn0; exact Nat.zero_le _
  · have h1 : int_mem_h_fold_sumset h ({0, p, q} : Finset ℤ) 1 := hn 1 hn1
    obtain ⟨f, hf, hsum⟩ := h1
    obtain ⟨i, j, hij, he⟩ := postage_stamp_number_two_eq_forward h p q hp0 hq0 hpq' f hf
    have hc : (1:ℤ) = (i:ℤ)*p + (j:ℤ)*q := by rw [← he, hsum]
    have hj0 : j = 0 := by
      by_contra hj
      have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.2 hj
      have hjZ : (1:ℤ) ≤ (j:ℤ) := by exact_mod_cast hj1
      have hq2 : (2:ℤ) ≤ q := by linarith
      have hi : (0:ℤ) ≤ (i:ℤ) := by positivity
      nlinarith [mul_nonneg hi (le_of_lt hp)]
    subst hj0
    simp only [Nat.cast_zero, zero_mul, add_zero] at hc
    have hp1 : p = 1 := by
      by_contra hne
      have hp2 : (2:ℤ) ≤ p := by omega
      rcases Nat.eq_zero_or_pos i with hi | hi
      · subst hi; simp at hc
      · have hi1 : (1:ℤ) ≤ (i:ℤ) := by exact_mod_cast hi
        nlinarith
    subst hp1
    have hq_nonneg : (0:ℤ) ≤ q := by linarith
    have hqcast : ((q.toNat : ℕ) : ℤ) = q := Int.toNat_of_nonneg hq_nonneg
    have hq2' : (2:ℤ) ≤ q := by linarith
    have hq2 : 2 ≤ q.toNat := by
      have : ((2:ℕ):ℤ) ≤ (q.toNat:ℤ) := by push_cast; rwa [hqcast]
      exact_mod_cast this
    refine postage_stamp_number_two_eq_zero_one_bound h n hh q.toNat hq2 ?_
    intro m hm
    have hthis := hn m hm
    simpa [hqcast] using hthis

lemma postage_stamp_number_two_eq_range_le (h : ℕ) (hh : 1 ≤ h) (A : Finset ℤ) (hcard : A.card = 3)
    (hnn : ∀ a ∈ A, 0 ≤ a) : postage_stamp_basis_range h A ≤ (h^2+6*h+1)/4 := by
  rw [postage_stamp_basis_range]
  by_cases h0 : (0:ℤ) ∈ A
  · have hcard0 : (A.erase 0).card = 2 := by
      rw [Finset.card_erase_of_mem h0, hcard]
    obtain ⟨p, q, hpq, heq⟩ := Finset.card_eq_two.1 hcard0
    have hpErase : p ∈ A.erase 0 := by rw [heq]; simp
    have hqErase : q ∈ A.erase 0 := by rw [heq]; simp
    rw [Finset.mem_erase] at hpErase hqErase
    have hp : 0 < p := lt_of_le_of_ne (hnn p hpErase.2) (Ne.symm hpErase.1)
    have hq : 0 < q := lt_of_le_of_ne (hnn q hqErase.2) (Ne.symm hqErase.1)
    have hAeq : A = ({0, p, q} : Finset ℤ) := by rw [← heq, Finset.insert_erase h0]
    have hne : ({n : ℕ | ∀ m : ℕ, m ≤ n → int_mem_h_fold_sumset h A (m:ℤ)}).Nonempty := by
      refine ⟨0, ?_⟩
      intro m hm
      have hm0 : m = 0 := by omega
      subst hm0
      exact ⟨fun _ => 0, fun i => by simp [h0], by simp⟩
    refine csSup_le hne ?_
    intro n hn
    rcases lt_or_gt_of_ne hpq with hlt | hlt
    · exact postage_stamp_number_two_eq_pair_bound h hh p q hp hlt n (fun m hm => by rw [← hAeq]; exact hn m hm)
    · refine postage_stamp_number_two_eq_pair_bound h hh q p hq hlt n (fun m hm => ?_)
      have h1 := hn m hm
      rw [hAeq] at h1
      rw [show (({0, p, q} : Finset ℤ)) = ({0, q, p} : Finset ℤ) from by
        ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto] at h1
      exact h1
  · have hempty : {n : ℕ | ∀ m : ℕ, m ≤ n → int_mem_h_fold_sumset h A (m:ℤ)} = ∅ := by
      ext n
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_forall]
      refine ⟨0, Nat.zero_le n, ?_⟩
      intro hz
      obtain ⟨f, hf, hsum⟩ := hz
      have ha1 : ∀ a ∈ A, (1:ℤ) ≤ a := by
        intro a ha
        have h1 : 0 ≤ a := hnn a ha
        have h2 : a ≠ 0 := fun hh' => h0 (hh' ▸ ha)
        omega
      have hle : (h:ℤ) ≤ ∑ i, f i := by
        calc (h:ℤ) = ∑ i : Fin h, (1:ℤ) := by simp
        _ ≤ ∑ i, f i := Finset.sum_le_sum (fun i _ => ha1 (f i) (hf i))
      rw [hsum] at hle
      have h1h : (1:ℤ) ≤ (h:ℤ) := by exact_mod_cast hh
      simp only [Nat.cast_zero] at hle
      linarith
    rw [hempty, csSup_empty]
    exact bot_le

lemma postage_stamp_number_two_eq_witness_odd (m : ℕ) :
    ∃ A : Finset ℤ, A.card = 3 ∧ (∀ a ∈ A, 0 ≤ a) ∧
      postage_stamp_basis_range (2*m+1) A = ((2*m+1)^2 + 6*(2*m+1) + 1)/4 := by
  have hcardA : ({0, 1, (m:ℤ)+2} : Finset ℤ).card = 3 := by
    refine Finset.card_eq_three.2 ⟨0, 1, (m:ℤ)+2, by norm_num, ?_, ?_, rfl⟩
    · have : (0:ℤ) ≤ (m:ℤ) := Nat.cast_nonneg m; omega
    · have : (0:ℤ) ≤ (m:ℤ) := Nat.cast_nonneg m; omega
  have hnnA : ∀ a ∈ ({0, 1, (m:ℤ)+2} : Finset ℤ), 0 ≤ a := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · norm_num
    · norm_num
    · positivity
  refine ⟨_, hcardA, hnnA, le_antisymm ?_ ?_⟩
  · exact postage_stamp_number_two_eq_range_le (2*m+1) (by omega) _ hcardA hnnA
  · have hge := postage_stamp_basis_range_zero_one_ge_of_odd m
    have hB : ((2*m+1)^2 + 6*(2*m+1) + 1)/4 = m^2+4*m+2 := by
      have h : (2*m+1)^2 + 6*(2*m+1) + 1 = 4*(m^2+4*m+2) := by ring
      omega
    rw [hB]
    exact hge

lemma postage_stamp_number_two_eq_witness_mod_four_two (u : ℕ) :
    ∃ A : Finset ℤ, A.card = 3 ∧ (∀ a ∈ A, 0 ≤ a) ∧
      postage_stamp_basis_range (4*u+2) A = ((4*u+2)^2 + 6*(4*u+2) + 1)/4 := by
  have hcardA : ({0, 1, 2*((u:ℤ)+1)} : Finset ℤ).card = 3 := by
    refine Finset.card_eq_three.2 ⟨0, 1, 2*((u:ℤ)+1), by norm_num, ?_, ?_, rfl⟩
    · have : (0:ℤ) ≤ 2*((u:ℤ)+1) := by positivity
      omega
    · have : (0:ℤ) < 2*((u:ℤ)+1) := by positivity
      omega
  have hnnA : ∀ a ∈ ({0, 1, 2*((u:ℤ)+1)} : Finset ℤ), 0 ≤ a := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · norm_num
    · norm_num
    · positivity
  refine ⟨_, hcardA, hnnA, le_antisymm ?_ ?_⟩
  · exact postage_stamp_number_two_eq_range_le (4*u+2) (by omega) _ hcardA hnnA
  · have hge := postage_stamp_basis_range_zero_one_ge_of_mod_four_eq_two (u+1) (by omega)
    have hcast : (((u+1 : ℕ)) : ℤ) = (u:ℤ) + 1 := by push_cast; ring
    have h4 : 4*(u+1) - 2 = 4*u+2 := by omega
    have hu2 : u+1+1 = u+2 := by omega
    rw [hcast, h4, hu2] at hge
    have hB : ((4*u+2)^2 + 6*(4*u+2) + 1)/4 = (u+2)*(4*u+2) := by
      have h1 : 4 * ((u+2)*(4*u+2)) ≤ (4*u+2)^2 + 6*(4*u+2) + 1 := by nlinarith
      have h2 : (4*u+2)^2 + 6*(4*u+2) + 1 < 4 * ((u+2)*(4*u+2) + 1) := by nlinarith
      omega
    rw [hB]
    exact hge

lemma postage_stamp_number_two_eq_witness_mod_four_zero (w : ℕ) (hw : 1 ≤ w) :
    ∃ A : Finset ℤ, A.card = 3 ∧ (∀ a ∈ A, 0 ≤ a) ∧
      postage_stamp_basis_range (4*w) A = ((4*w)^2 + 6*(4*w) + 1)/4 := by
  have hcardA : ({0, 1, 2*(w:ℤ)+1} : Finset ℤ).card = 3 := by
    refine Finset.card_eq_three.2 ⟨0, 1, 2*(w:ℤ)+1, by norm_num, ?_, ?_, rfl⟩
    · have : (0:ℤ) ≤ 2*(w:ℤ) := by positivity
      omega
    · have : (0:ℤ) < 2*(w:ℤ)+1 := by positivity
      omega
  have hnnA : ∀ a ∈ ({0, 1, 2*(w:ℤ)+1} : Finset ℤ), 0 ≤ a := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · norm_num
    · norm_num
    · positivity
  refine ⟨_, hcardA, hnnA, le_antisymm ?_ ?_⟩
  · exact postage_stamp_number_two_eq_range_le (4*w) (by omega) _ hcardA hnnA
  · have hge := postage_stamp_basis_range_zero_one_ge_of_mod_four_eq_zero w hw
    have hB : ((4*w)^2 + 6*(4*w) + 1)/4 = w*(4*w+6) := by
      have h1 : 4 * (w*(4*w+6)) ≤ (4*w)^2 + 6*(4*w) + 1 := by nlinarith
      have h2 : (4*w)^2 + 6*(4*w) + 1 < 4 * (w*(4*w+6) + 1) := by nlinarith
      omega
    rw [hB]
    exact hge

theorem postage_stamp_number_two_eq (h : ℕ) (hh : 1 ≤ h) :
    postage_stamp_number h 2 = (h ^ 2 + 6 * h + 1) / 4 := by
  unfold postage_stamp_number
  apply le_antisymm
  · refine csSup_le ⟨postage_stamp_basis_range h ({0,1,2} : Finset ℤ), ?_⟩ ?_
    · exact ⟨{0,1,2}, by decide,
        by intro a ha; simp only [Finset.mem_insert, Finset.mem_singleton] at ha; omega, rfl⟩
    · rintro n ⟨A, hcard, hnn, rfl⟩
      exact postage_stamp_number_two_eq_range_le h hh A hcard hnn
  · have hbdd : BddAbove {n : ℕ | ∃ A : Finset ℤ, A.card = 2 + 1 ∧ (∀ a ∈ A, 0 ≤ a) ∧
        postage_stamp_basis_range h A = n} := by
      refine ⟨3^h, ?_⟩
      rintro n ⟨A, hcard, hnn, rfl⟩
      have hne : A.Nonempty := Finset.card_pos.mp (by omega)
      have hle := postage_stamp_basis_range_succ_le_card_pow h A hne
      have hle' : postage_stamp_basis_range h A + 1 ≤ 3^h := by
        rw [hcard] at hle
        simpa using hle
      omega
    refine le_csSup hbdd ?_
    by_cases hodd : h % 2 = 1
    · obtain ⟨A, hc, hn, he⟩ := postage_stamp_number_two_eq_witness_odd (h/2)
      refine ⟨A, hc, hn, ?_⟩
      rw [show h = 2*(h/2)+1 from by omega]
      exact he
    · by_cases h4 : h % 4 = 0
      · obtain ⟨A, hc, hn, he⟩ := postage_stamp_number_two_eq_witness_mod_four_zero (h/4) (by omega)
        refine ⟨A, hc, hn, ?_⟩
        rw [show h = 4*(h/4) from by omega]
        exact he
      · obtain ⟨A, hc, hn, he⟩ := postage_stamp_number_two_eq_witness_mod_four_two ((h-2)/4)
        refine ⟨A, hc, hn, ?_⟩
        rw [show h = 4*((h-2)/4)+2 from by omega]
        exact he
