import AFTD.Prelude

/-!
# f2_subset_le_four_universal_spectrum

Topic: combinatorics   Node: 5715b250aa2c

Provenance: formalization of a published result. Source: arXiv:2610.24022, Lemma 3.3

For every natural number d and every subset T of Fin d → ZMod 2 with cardinality 1, 2, or 4, there exists a subset B of Fin d → ZMod 2 such that |B| * |T| = 2^d and for all distinct b, b' ∈ B, the character sum ∑ t ∈ T, (-1 : ℤ) ^ (dotProduct (b + b') t).val is nonzero.
-/

open scoped Matrix

lemma f2_subset_le_four_universal_spectrum_zmod2_eq_zero_or_one (c : ZMod 2) :
    c = 0 ∨ c = 1 := by
  have h : c.val < 2 := ZMod.val_lt c
  have hc : ((c.val : ℕ) : ZMod 2) = c := ZMod.natCast_zmod_val c
  interval_cases c.val
  · left; rw [← hc]; norm_num
  · right; rw [← hc]; norm_num

lemma f2_subset_le_four_universal_spectrum_zmod2_add_eq_zero_iff (a b : ZMod 2) :
    a + b = 0 ↔ a = b := by
  constructor
  · intro h
    rw [← neg_eq_of_add_eq_zero_left h]
    exact CharTwo.neg_eq b
  · intro h; rw [h]; exact CharTwo.add_self_eq_zero b

lemma f2_subset_le_four_universal_spectrum_add_self_eq_zero_fun (d : ℕ) (z : Fin d → ZMod 2) :
    z + z = 0 := by
  funext j; simp only [Pi.add_apply, Pi.zero_apply]; exact CharTwo.add_self_eq_zero (z j)

lemma f2_subset_le_four_universal_spectrum_neg_eq_self_fun (d : ℕ) (z : Fin d → ZMod 2) :
    -z = z := by
  funext j; simp only [Pi.neg_apply]; exact CharTwo.neg_eq (z j)

lemma f2_subset_le_four_universal_spectrum_add_eq_zero_iff (d : ℕ)
    (a b : Fin d → ZMod 2) : a + b = 0 ↔ a = b := by
  constructor
  · intro h
    rw [← neg_eq_of_add_eq_zero_left h]
    exact f2_subset_le_four_universal_spectrum_neg_eq_self_fun d b
  · intro h
    rw [h]
    exact f2_subset_le_four_universal_spectrum_add_self_eq_zero_fun d b

lemma f2_subset_le_four_universal_spectrum_chi_ne_zero (z : ZMod 2) :
    (-1 : ℤ) ^ z.val ≠ 0 := by
  have h : z.val < 2 := ZMod.val_lt z
  interval_cases z.val <;> simp

lemma f2_subset_le_four_universal_spectrum_chi_pm_one (z : ZMod 2) :
    (-1 : ℤ) ^ z.val = 1 ∨ (-1 : ℤ) ^ z.val = -1 := by
  have h : z.val < 2 := ZMod.val_lt z
  interval_cases z.val
  · left; simp
  · right; simp

lemma f2_subset_le_four_universal_spectrum_card_hyperplane (d : ℕ) (v : Fin d → ZMod 2)
    (hv : v ≠ 0) :
    2 * (Finset.univ.filter (fun x => x ⬝ᵥ v = 0)).card = 2^d := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hv (funext h)
  have hi1 : v i = 1 := (f2_subset_le_four_universal_spectrum_zmod2_eq_zero_or_one (v i)).resolve_left hi
  set e : Fin d → ZMod 2 := Pi.single i 1 with he
  have hev : e ⬝ᵥ v = 1 := by rw [he, single_dotProduct]; simp [hi1]
  have hee : e + e = 0 := f2_subset_le_four_universal_spectrum_add_self_eq_zero_fun d e
  have hbij : (Finset.univ.filter (fun x => x ⬝ᵥ v = 0)).card
      = (Finset.univ.filter (fun x => x ⬝ᵥ v = 1)).card := by
    apply Finset.card_bij (fun x _ => x + e)
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [add_dotProduct, hx, hev]; decide
    · intro x1 _ x2 _ h
      exact add_right_cancel h
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      refine ⟨y + e, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [add_dotProduct, hy, hev]; decide
      · show y + e + e = y
        rw [add_assoc, hee, add_zero]
  have hnot : (Finset.univ.filter (fun x => ¬ (x ⬝ᵥ v = 0)))
      = (Finset.univ.filter (fun x => x ⬝ᵥ v = 1)) := by
    apply Finset.filter_congr
    intro x _
    constructor
    · intro h; exact (f2_subset_le_four_universal_spectrum_zmod2_eq_zero_or_one (x ⬝ᵥ v)).resolve_left h
    · intro h h0; rw [h0] at h; exact absurd h (by decide)
  have hpart : (Finset.univ.filter (fun x => x ⬝ᵥ v = 0)).card
      + (Finset.univ.filter (fun x => ¬ (x ⬝ᵥ v = 0))).card
      = Fintype.card (Fin d → ZMod 2) := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ]
  have hV : Fintype.card (Fin d → ZMod 2) = 2^d := by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
  rw [hV, hnot, ← hbij] at hpart
  omega

lemma f2_subset_le_four_universal_spectrum_exists_dotProduct_pair (d : ℕ)
    (a b : Fin d → ZMod 2) (_ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    ∃ x, x ⬝ᵥ a = 0 ∧ x ⬝ᵥ b = 1 := by
  by_cases h : ∃ j, b j ≠ 0 ∧ a j = 0
  · obtain ⟨j, hbj, haj⟩ := h
    refine ⟨Pi.single j 1, ?_, ?_⟩
    · rw [single_dotProduct, haj, mul_zero]
    · rw [single_dotProduct, one_mul]
      exact (f2_subset_le_four_universal_spectrum_zmod2_eq_zero_or_one (b j)).resolve_left hbj
  · have h' : ∀ j, b j ≠ 0 → a j ≠ 0 := by
      intro j hbj haj; exact h ⟨j, hbj, haj⟩
    obtain ⟨j, hbj⟩ : ∃ j, b j ≠ 0 := by
      by_contra hh; simp only [not_exists, not_not] at hh; exact hb (funext hh)
    obtain ⟨i, hi⟩ : ∃ i, a i ≠ b i := by
      by_contra hh; simp only [not_exists, not_not] at hh; exact hab (funext hh)
    have hbi : b i = 0 := by
      rcases f2_subset_le_four_universal_spectrum_zmod2_eq_zero_or_one (b i) with h0 | h1
      · exact h0
      · exfalso
        have hai : a i ≠ 0 := h' i (by rw [h1]; exact one_ne_zero)
        have hai1 : a i = 1 := (f2_subset_le_four_universal_spectrum_zmod2_eq_zero_or_one (a i)).resolve_left hai
        exact hi (by rw [hai1, h1])
    have hai : a i = 1 := by
      rcases f2_subset_le_four_universal_spectrum_zmod2_eq_zero_or_one (a i) with h0 | h1
      · exact absurd (by rw [h0, hbi] : a i = b i) hi
      · exact h1
    have haj : a j = 1 := (f2_subset_le_four_universal_spectrum_zmod2_eq_zero_or_one (a j)).resolve_left (h' j hbj)
    have hbj1 : b j = 1 := (f2_subset_le_four_universal_spectrum_zmod2_eq_zero_or_one (b j)).resolve_left hbj
    have hij : i ≠ j := by intro hij; rw [hij] at hbi; exact hbj hbi
    refine ⟨Pi.single i 1 + Pi.single j 1, ?_, ?_⟩
    · rw [add_dotProduct, single_dotProduct, single_dotProduct, hai, haj]; decide
    · rw [add_dotProduct, single_dotProduct, single_dotProduct, hbi, hbj1]; decide

lemma f2_subset_le_four_universal_spectrum_card_hyperplane_pair (d : ℕ)
    (a b : Fin d → ZMod 2) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    4 * (Finset.univ.filter (fun x => x ⬝ᵥ a = 0 ∧ x ⬝ᵥ b = 0)).card = 2^d := by
  obtain ⟨x0, hx0a, hx0b⟩ := f2_subset_le_four_universal_spectrum_exists_dotProduct_pair d a b ha hb hab
  set s := Finset.univ.filter (fun x => x ⬝ᵥ a = 0) with hs
  have hcard_s : 2 * s.card = 2^d := f2_subset_le_four_universal_spectrum_card_hyperplane d a ha
  have hx00 : x0 + x0 = 0 := f2_subset_le_four_universal_spectrum_add_self_eq_zero_fun d x0
  have hbij : (s.filter (fun x => x ⬝ᵥ b = 0)).card = (s.filter (fun x => ¬ (x ⬝ᵥ b = 0))).card := by
    apply Finset.card_bij (fun x _ => x + x0)
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hs] at hx ⊢
      obtain ⟨hxa, hxb⟩ := hx
      refine ⟨?_, ?_⟩
      · rw [add_dotProduct, hxa, hx0a]; decide
      · rw [add_dotProduct, hxb, hx0b]; decide
    · intro x1 _ x2 _ h; exact add_right_cancel h
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hs] at hy
      obtain ⟨hya, hyb⟩ := hy
      have hyb1 : y ⬝ᵥ b = 1 := (f2_subset_le_four_universal_spectrum_zmod2_eq_zero_or_one (y ⬝ᵥ b)).resolve_left hyb
      refine ⟨y + x0, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, hs]
        refine ⟨?_, ?_⟩
        · rw [add_dotProduct, hya, hx0a]; decide
        · rw [add_dotProduct, hyb1, hx0b]; decide
      · show y + x0 + x0 = y
        rw [add_assoc, hx00, add_zero]
  have hpartition : (s.filter (fun x => x ⬝ᵥ b = 0)).card
      + (s.filter (fun x => ¬ (x ⬝ᵥ b = 0))).card = s.card := by
    rw [Finset.card_filter_add_card_filter_not]
  rw [hbij] at hpartition
  have hp0 : 2 * (s.filter (fun x => x ⬝ᵥ b = 0)).card = s.card := by omega
  have hEq : (s.filter (fun x => x ⬝ᵥ b = 0))
      = (Finset.univ.filter (fun x => x ⬝ᵥ a = 0 ∧ x ⬝ᵥ b = 0)) := by
    rw [hs, Finset.filter_filter]
  rw [hEq] at hp0
  omega

lemma f2_subset_le_four_universal_spectrum_case_one (d : ℕ) (T : Finset (Fin d → ZMod 2))
    (hT : T.card = 1) :
    ∃ B : Finset (Fin d → ZMod 2), B.card * T.card = 2^d ∧
      ∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → ∑ t ∈ T, (-1:ℤ)^(dotProduct (b+b') t).val ≠ 0 := by
  obtain ⟨t, rfl⟩ := Finset.card_eq_one.mp hT
  refine ⟨Finset.univ, ?_, ?_⟩
  · rw [Finset.card_singleton, mul_one, Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  · intro b _ b' _ _
    rw [Finset.sum_singleton]
    exact f2_subset_le_four_universal_spectrum_chi_ne_zero _

lemma f2_subset_le_four_universal_spectrum_case_two (d : ℕ) (T : Finset (Fin d → ZMod 2))
    (hT : T.card = 2) :
    ∃ B : Finset (Fin d → ZMod 2), B.card * T.card = 2^d ∧
      ∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → ∑ t ∈ T, (-1:ℤ)^(dotProduct (b+b') t).val ≠ 0 := by
  obtain ⟨t1, t2, ht12, rfl⟩ := Finset.card_eq_two.mp hT
  have hv : t1 + t2 ≠ 0 := by
    intro h
    exact ht12 ((f2_subset_le_four_universal_spectrum_add_eq_zero_iff d t1 t2).mp h)
  refine ⟨Finset.univ.filter (fun x => x ⬝ᵥ (t1 + t2) = 0), ?_, ?_⟩
  · have hcard := f2_subset_le_four_universal_spectrum_card_hyperplane d (t1 + t2) hv
    rw [Finset.card_pair ht12]
    omega
  · intro b hb b' hb' hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb hb'
    have hx : (b + b') ⬝ᵥ (t1 + t2) = 0 := by rw [add_dotProduct, hb, hb', add_zero]
    have hsum0 : (b + b') ⬝ᵥ t1 + (b + b') ⬝ᵥ t2 = 0 := by
      rw [← dotProduct_add]; exact hx
    have heq : (b + b') ⬝ᵥ t1 = (b + b') ⬝ᵥ t2 :=
      (f2_subset_le_four_universal_spectrum_zmod2_add_eq_zero_iff ((b + b') ⬝ᵥ t1) ((b + b') ⬝ᵥ t2)).mp hsum0
    rw [Finset.sum_pair ht12, heq]
    have hchi := f2_subset_le_four_universal_spectrum_chi_ne_zero ((b + b') ⬝ᵥ t2)
    have hdbl : (-1:ℤ)^((b+b')⬝ᵥt2).val + (-1:ℤ)^((b+b')⬝ᵥt2).val
        = 2 * (-1:ℤ)^((b+b')⬝ᵥt2).val := by ring
    rw [hdbl]
    exact mul_ne_zero (by norm_num) hchi

lemma f2_subset_le_four_universal_spectrum_case_four (d : ℕ) (T : Finset (Fin d → ZMod 2))
    (hT : T.card = 4) :
    ∃ B : Finset (Fin d → ZMod 2), B.card * T.card = 2^d ∧
      ∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → ∑ t ∈ T, (-1:ℤ)^(dotProduct (b+b') t).val ≠ 0 := by
  obtain ⟨t0, t1, t2, t3, h01, h02, h03, h12, h13, h23, rfl⟩ := Finset.card_eq_four.mp hT
  have ha0 : t1 + t0 ≠ 0 := by
    intro h
    exact h01 ((f2_subset_le_four_universal_spectrum_add_eq_zero_iff d t1 t0).mp h).symm
  have hb0 : t2 + t0 ≠ 0 := by
    intro h
    exact h02 ((f2_subset_le_four_universal_spectrum_add_eq_zero_iff d t2 t0).mp h).symm
  have hab : t1 + t0 ≠ t2 + t0 := by
    intro h; exact h12 (add_right_cancel h)
  refine ⟨Finset.univ.filter (fun x => x ⬝ᵥ (t1 + t0) = 0 ∧ x ⬝ᵥ (t2 + t0) = 0), ?_, ?_⟩
  · have hcard := f2_subset_le_four_universal_spectrum_card_hyperplane_pair d (t1 + t0) (t2 + t0) ha0 hb0 hab
    rw [hT]
    omega
  · intro b hb b' hb' hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb hb'
    obtain ⟨hba, hbb⟩ := hb
    obtain ⟨hb'a, hb'b⟩ := hb'
    have hxa : (b + b') ⬝ᵥ (t1 + t0) = 0 := by rw [add_dotProduct, hba, hb'a, add_zero]
    have hxb : (b + b') ⬝ᵥ (t2 + t0) = 0 := by rw [add_dotProduct, hbb, hb'b, add_zero]
    have ht1 : (b + b') ⬝ᵥ t1 = (b + b') ⬝ᵥ t0 := by
      have hsplit : t1 = (t1 + t0) + t0 := by
        rw [add_assoc, f2_subset_le_four_universal_spectrum_add_self_eq_zero_fun d t0, add_zero]
      rw [hsplit, dotProduct_add, hxa, zero_add]
    have ht2 : (b + b') ⬝ᵥ t2 = (b + b') ⬝ᵥ t0 := by
      have hsplit : t2 = (t2 + t0) + t0 := by
        rw [add_assoc, f2_subset_le_four_universal_spectrum_add_self_eq_zero_fun d t0, add_zero]
      rw [hsplit, dotProduct_add, hxb, zero_add]
    rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
    · rw [ht1, ht2]
      rcases f2_subset_le_four_universal_spectrum_chi_pm_one ((b + b') ⬝ᵥ t0) with hp | hp <;>
        rcases f2_subset_le_four_universal_spectrum_chi_pm_one ((b + b') ⬝ᵥ t3) with hq | hq <;>
        rw [hp, hq] <;> norm_num
    · simp [h23]
    · simp [h12, h13]
    · simp [h01, h02, h03]

open scoped Matrix in
/-- Existence of a dual spectrum avoiding character zeros for subsets of size 1, 2, or 4 in (ZMod 2)^d. -/
theorem f2_subset_le_four_universal_spectrum (d : ℕ)
    (T : Finset (Fin d → ZMod 2)) (hT : T.card = 1 ∨ T.card = 2 ∨ T.card = 4) :
    ∃ B : Finset (Fin d → ZMod 2), B.card * T.card = 2 ^ d ∧
      ∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → ∑ t ∈ T, (-1 : ℤ) ^ (dotProduct (b + b') t).val ≠ 0 := by
  rcases hT with h1 | h2 | h4
  · exact f2_subset_le_four_universal_spectrum_case_one d T h1
  · exact f2_subset_le_four_universal_spectrum_case_two d T h2
  · exact f2_subset_le_four_universal_spectrum_case_four d T h4
