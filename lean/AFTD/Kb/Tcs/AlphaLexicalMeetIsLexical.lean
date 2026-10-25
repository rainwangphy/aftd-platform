import AFTD.Prelude
import AFTD.Kb.Tcs.AlphaSignedCell
import AFTD.Kb.Tcs.AlphaLexicalLt
import AFTD.Kb.Tcs.AlphaIsLexical
import AFTD.Kb.Tcs.AlphaLexicalMeet

/-!
# alpha_lexical_meet_is_lexical

Topic: combinatorics   Node: 585b270212ef

Provenance: helper lemma. A helper for the lexical-sequence route to OP-392, arXiv:2610.24758, Conjecture 1. It discharges the lexical-meet hypothesis of arXiv:0810.5205, Theorem 3.1. This proof is supplied directly; no research advance is claimed.

The source common-prefix meet of two nonempty positive lexical sequences is lexical, even if their sums differ.
-/

theorem alpha_meet_aux_get_d_drop (a : List ℕ) (k j : ℕ) :
    (a.drop k).getD j 0 = a.getD (k + j) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem alpha_meet_aux_signed_eq {a b : List ℕ} {i : ℕ}
    (h : a.getD i 0 = b.getD i 0) :
    alpha_signed_cell a i = alpha_signed_cell b i := by
  simp only [alpha_signed_cell, h]

theorem alpha_meet_aux_not_lt_of_first_difference (a b : List ℕ) (i : ℕ)
    (he : ∀ j < i, alpha_signed_cell a j = alpha_signed_cell b j)
    (hg : alpha_signed_cell b i < alpha_signed_cell a i) :
    ¬ alpha_lexical_lt a b := by
  rintro ⟨j, hj, he', hl⟩
  rcases lt_trichotomy j i with hji | rfl | hij
  · have := he j hji
    omega
  · omega
  · have := he' i hij
    omega

theorem alpha_meet_aux_lexical_of_prefix_branch (f a b : List ℕ)
    (hfne : f ≠ []) (hfpos : ∀ v ∈ f, 0 < v)
    (hla : f.length ≤ a.length) (hlb : f.length ≤ b.length)
    (ha : alpha_is_lexical a) (hb : alpha_is_lexical b)
    (haf : ∀ j < f.length, a.getD j 0 = f.getD j 0)
    (hbf : ∀ j < f.length - 1, b.getD j 0 = f.getD j 0)
    (hlast : f.getD (f.length - 1) 0 < b.getD (f.length - 1) 0) :
    alpha_is_lexical f := by
  refine ⟨hfne, hfpos, ?_⟩
  intro k hk hk0
  let q := f.length - k
  have hq0 : 0 < q := by dsimp [q]; omega
  have hql : q < f.length := by dsimp [q]; omega
  have hqk : k + q = f.length := by dsimp [q]; omega
  have hfa (j : ℕ) (hj : j < f.length) :
      alpha_signed_cell a j = alpha_signed_cell f j :=
    alpha_meet_aux_signed_eq (haf j hj)
  have hfad (j : ℕ) (hj : j < q) :
      alpha_signed_cell (a.drop k) j = alpha_signed_cell (f.drop k) j := by
    apply alpha_meet_aux_signed_eq
    simp only [alpha_meet_aux_get_d_drop]
    exact haf _ (by omega)
  obtain ⟨i, hi, he, hlt⟩ := ha.2.2 k (by omega) hk0
  by_cases hiq : i < q
  · refine ⟨i, ?_, ?_, ?_⟩
    · have : i < f.length := by omega
      exact lt_of_lt_of_le this (le_max_right _ _)
    · intro j hj
      rw [← hfad j (by omega), ← hfa j (by omega)]
      exact he j hj
    · rw [← hfad i hiq, ← hfa i (by omega)]
      exact hlt
  · have hborder (j : ℕ) (hj : j < q) :
        alpha_signed_cell (f.drop k) j = alpha_signed_cell f j := by
      rw [← hfad j hj, ← hfa j (by omega)]
      exact he j (by omega)
    by_cases hqe : q % 2 = 0
    · refine ⟨q, lt_of_lt_of_le hql (le_max_right _ _), hborder, ?_⟩
      have hmem : f.getD q 0 ∈ f := by
        rw [List.getD_eq_getElem _ _ hql]
        exact List.getElem_mem hql
      have hp := hfpos _ hmem
      have hd : (f.drop k).getD q 0 = 0 :=
        List.getD_eq_default _ _ (by
          simpa only [List.length_drop] using
            (le_rfl : f.length - k ≤ f.length - k))
      simp only [alpha_signed_cell, hqe, if_true, hd, Nat.cast_zero]
      exact_mod_cast hp
    · have hj0 : (q - 1) % 2 = 0 := by omega
      have hjl : q - 1 < f.length - 1 := by omega
      have hjk : k + (q - 1) = f.length - 1 := by omega
      have hcross : f.getD (q - 1) 0 = f.getD (f.length - 1) 0 := by
        have h := hborder (q - 1) (by omega)
        simp only [alpha_signed_cell, hj0, if_true, alpha_meet_aux_get_d_drop, hjk] at h
        omega
      have hpre : ∀ j < q - 1,
          alpha_signed_cell (b.drop k) j = alpha_signed_cell b j := by
        intro j hj
        have h1 : alpha_signed_cell b j = alpha_signed_cell f j :=
          alpha_meet_aux_signed_eq (hbf j (by omega))
        have h2 : alpha_signed_cell (b.drop k) j =
            alpha_signed_cell (f.drop k) j := by
          apply alpha_meet_aux_signed_eq
          simp only [alpha_meet_aux_get_d_drop]
          exact hbf _ (by omega)
        rw [h2, h1]
        exact hborder j (by omega)
      have hgreater : alpha_signed_cell b (q - 1) <
          alpha_signed_cell (b.drop k) (q - 1) := by
        simp only [alpha_signed_cell, hj0, if_true, alpha_meet_aux_get_d_drop, hjk]
        rw [hbf _ hjl, hcross]
        exact_mod_cast hlast
      exact False.elim ((alpha_meet_aux_not_lt_of_first_difference (b.drop k) b (q - 1)
        hpre hgreater) (hb.2.2 k (by omega) hk0))

theorem alpha_meet_aux_shape (a b : List ℕ) :
    alpha_lexical_meet a b = a ∨ alpha_lexical_meet a b = b ∨
      ∃ p x y s t, x ≠ y ∧ a = p ++ x :: s ∧ b = p ++ y :: t ∧
        alpha_lexical_meet a b = p ++ [min x y] := by
  induction a generalizing b with
  | nil => exact Or.inl rfl
  | cons x xs ih =>
    cases b with
    | nil => exact Or.inr (Or.inl rfl)
    | cons y ys =>
      by_cases hxy : x = y
      · subst y
        rcases ih ys with h | h | ⟨p, u, v, s, t, huv, hx, hy, hf⟩
        · exact Or.inl (by simp [alpha_lexical_meet, h])
        · exact Or.inr (Or.inl (by simp [alpha_lexical_meet, h]))
        · right; right
          exact ⟨x :: p, u, v, s, t, huv, by simp [hx], by simp [hy],
            by simp [alpha_lexical_meet, hf]⟩
      · exact Or.inr (Or.inr ⟨[], x, y, xs, ys, hxy, rfl, rfl,
          by simp [alpha_lexical_meet, hxy]⟩)

theorem alpha_meet_aux_branch (p s t : List ℕ) (x y : ℕ) (hxy : x < y)
    (ha : alpha_is_lexical (p ++ x :: s))
    (hb : alpha_is_lexical (p ++ y :: t)) :
    alpha_is_lexical (p ++ [x]) := by
  apply alpha_meet_aux_lexical_of_prefix_branch (p ++ [x]) (p ++ x :: s) (p ++ y :: t)
  · simp
  · intro v hv
    apply ha.2.1 v
    rcases List.mem_append.mp hv with hv | hv
    · exact List.mem_append.mpr (Or.inl hv)
    · have : v = x := by simpa using hv
      subst v
      simp
  · simp
  · simp
  · exact ha
  · exact hb
  · intro j hj
    have he : p ++ x :: s = (p ++ [x]) ++ s := by
      simp only [List.append_assoc, List.singleton_append]
    rw [he, List.getD_append _ _ _ _ hj]
  · intro j hj
    have hj' : j < p.length := by simpa using hj
    rw [List.getD_append p (y :: t) 0 j hj', List.getD_append p [x] 0 j hj']
  · simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel]
    rw [List.getD_append_right _ _ _ _ (le_refl _),
      List.getD_append_right _ _ _ _ (le_refl _)]
    simpa using hxy

theorem alpha_lexical_meet_is_lexical (a b : List ℕ) (ha : alpha_is_lexical a)
    (hb : alpha_is_lexical b) : alpha_is_lexical (alpha_lexical_meet a b) := by
  rcases alpha_meet_aux_shape a b with h | h | ⟨p, x, y, s, t, hxy, rfl, rfl, hf⟩
  · rwa [h]
  · rwa [h]
  · rw [hf]
    rcases lt_or_gt_of_ne hxy with hlt | hgt
    · rw [min_eq_left (le_of_lt hlt)]
      exact alpha_meet_aux_branch p s t x y hlt ha hb
    · rw [min_eq_right (le_of_lt hgt)]
      exact alpha_meet_aux_branch p t s y x hgt hb ha
