import AFTD.Prelude
import AFTD.Kb.Tcs.AlphaIsLexical
import AFTD.Kb.Tcs.AlphaLexicalLt
import AFTD.Kb.Tcs.AlphaSignedCell
import AFTD.Kb.Tcs.AlphaLexicalFirstNegativeStepExists
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# alpha_later_local_blocker_inherits_earlier

Topic: combinatorics   Node: e1add0fa9f0e

Provenance: helper lemma. Blocking-suffix inheritance for OP-392, arXiv:2610.24758; alternating lexical order and moves as in arXiv:0810.5205.

Every blocker of a later locally admissible even move is also a blocker of an earlier even move, with the same suffix-index parity after accounting for the inserted or deleted cell.
-/

theorem alpha_later_local_blocker_inherits_earlier_signed_cell_eq_zero_of_length_le (a : List ℕ) (i : ℕ) (h : a.length ≤ i) :
    alpha_signed_cell a i = 0 := by
  simp only [alpha_signed_cell]
  have : a.getD i 0 = 0 := List.getD_eq_default a 0 h
  rw [this]
  split_ifs <;> simp

theorem alpha_later_local_blocker_inherits_earlier_lexical_lt_trans (x y z : List ℕ)
    (hxy : alpha_lexical_lt x y) (hyz : alpha_lexical_lt y z) :
    alpha_lexical_lt x z := by
  rcases hxy with ⟨i, hi, hxy_eq, hxy_lt⟩
  rcases hyz with ⟨j, hj, hyz_eq, hyz_lt⟩
  rcases lt_trichotomy i j with hij | hij | hji
  · refine ⟨i, ?_, ?_, ?_⟩
    · have hne : alpha_signed_cell x i ≠ alpha_signed_cell z i := by
        rw [← hyz_eq i hij]
        linarith
      by_contra! hle
      have hx : alpha_signed_cell x i = 0 :=
        alpha_later_local_blocker_inherits_earlier_signed_cell_eq_zero_of_length_le x i (by omega)
      have hz : alpha_signed_cell z i = 0 :=
        alpha_later_local_blocker_inherits_earlier_signed_cell_eq_zero_of_length_le z i (by omega)
      exact hne (hx.trans hz.symm)
    · intro k hk
      rw [hxy_eq k hk, hyz_eq k (by omega)]
    · rw [← hyz_eq i hij]
      exact hxy_lt
  · subst hij
    refine ⟨i, ?_, ?_, ?_⟩
    · have hne : alpha_signed_cell x i ≠ alpha_signed_cell z i := by linarith
      by_contra! hle
      have hx : alpha_signed_cell x i = 0 :=
        alpha_later_local_blocker_inherits_earlier_signed_cell_eq_zero_of_length_le x i (by omega)
      have hz : alpha_signed_cell z i = 0 :=
        alpha_later_local_blocker_inherits_earlier_signed_cell_eq_zero_of_length_le z i (by omega)
      exact hne (hx.trans hz.symm)
    · intro k hk
      rw [hxy_eq k hk, hyz_eq k hk]
    · linarith
  · refine ⟨j, ?_, ?_, ?_⟩
    · have hne : alpha_signed_cell x j ≠ alpha_signed_cell z j := by
        rw [hxy_eq j hji]
        linarith
      by_contra! hle
      have hx : alpha_signed_cell x j = 0 :=
        alpha_later_local_blocker_inherits_earlier_signed_cell_eq_zero_of_length_le x j (by omega)
      have hz : alpha_signed_cell z j = 0 :=
        alpha_later_local_blocker_inherits_earlier_signed_cell_eq_zero_of_length_le z j (by omega)
      exact hne (hx.trans hz.symm)
    · intro k hk
      rw [hxy_eq k (by omega), hyz_eq k hk]
    · rw [hxy_eq j hji]
      exact hyz_lt

theorem alpha_later_local_blocker_inherits_earlier_drop_d_eq_a (a : List ℕ) (j k : ℕ) (hj0 : 0 < j) (hj : j < a.length)
    (hklen : k < (if 1 < a.getD j 0 then a.take j ++ [a.getD j 0 - 1, 1] ++ a.drop (j + 1)
                  else a.take (j - 1) ++ [a.getD (j - 1) 0 + 1] ++ a.drop (j + 1)).length)
    (hbound : (if 1 < a.getD j 0 then j + 1 else j - 1) < k) :
    let d := if 1 < a.getD j 0 then a.take j ++ [a.getD j 0 - 1, 1] ++ a.drop (j + 1)
             else a.take (j - 1) ++ [a.getD (j - 1) 0 + 1] ++ a.drop (j + 1)
    let r := if 1 < a.getD j 0 then k - 1 else k + 1
    j < r ∧ r < a.length ∧ d.drop k = a.drop r := by
  dsimp only
  split_ifs at hklen hbound ⊢ with hjc
  · have hlen : (a.take j ++ [a.getD j 0 - 1, 1] ++ a.drop (j + 1)).length = a.length + 1 := by
      rw [List.length_append, List.length_append, List.length_take, List.length_drop]; simp; omega
    have hk2 : j + 2 ≤ k := by omega
    have hr_lt : k - 1 < a.length := by omega
    have hr_gt : j < k - 1 := by omega
    refine ⟨hr_gt, hr_lt, ?_⟩
    rw [List.drop_append, List.drop_append]
    have h1 : (a.take j).length = j := by rw [List.length_take]; omega
    have h2 : (a.take j ++ [a.getD j 0 - 1, 1]).length = j + 2 := by
      rw [List.length_append, h1]; simp
    rw [h1, h2]
    have hd1 : List.drop k (a.take j) = [] := List.drop_eq_nil_of_le (by omega)
    rw [hd1, List.nil_append]
    have hd2 : List.drop (k - j) [a.getD j 0 - 1, 1] = [] := by
      apply List.drop_eq_nil_of_le; simp; omega
    rw [hd2, List.nil_append, List.drop_drop]
    congr 1
    omega
  · have hlen : (a.take (j - 1) ++ [a.getD (j - 1) 0 + 1] ++ a.drop (j + 1)).length = a.length - 1 := by
      rw [List.length_append, List.length_append, List.length_take, List.length_drop]; simp; omega
    have hk2 : j ≤ k := by omega
    have hr_lt : k + 1 < a.length := by omega
    have hr_gt : j < k + 1 := by omega
    refine ⟨hr_gt, hr_lt, ?_⟩
    rw [List.drop_append, List.drop_append]
    have h1 : (a.take (j - 1)).length = j - 1 := by rw [List.length_take]; omega
    have h2 : (a.take (j - 1) ++ [a.getD (j - 1) 0 + 1]).length = j := by
      rw [List.length_append, h1]; simp; omega
    rw [h1, h2]
    have hd1 : List.drop k (a.take (j - 1)) = [] := List.drop_eq_nil_of_le (by omega)
    rw [hd1, List.nil_append]
    have hd2 : List.drop (k - (j - 1)) [a.getD (j - 1) 0 + 1] = [] := by
      apply List.drop_eq_nil_of_le; simp; omega
    rw [hd2, List.nil_append, List.drop_drop]
    congr 1
    omega

theorem alpha_later_local_blocker_inherits_earlier_drop_c_eq_a (a : List ℕ) (i r : ℕ) (hi0 : 0 < i) (hi : i < a.length)
    (hir : i + 1 < r) (hr : r < a.length) :
    let c := if 1 < a.getD i 0 then a.take i ++ [a.getD i 0 - 1, 1] ++ a.drop (i + 1)
             else a.take (i - 1) ++ [a.getD (i - 1) 0 + 1] ++ a.drop (i + 1)
    let b := if 1 < a.getD i 0 then r + 1 else r - 1
    b < c.length ∧ c.drop b = a.drop r := by
  dsimp only
  split_ifs with hic
  · have hlen : (a.take i ++ [a.getD i 0 - 1, 1] ++ a.drop (i + 1)).length = a.length + 1 := by
      rw [List.length_append, List.length_append, List.length_take, List.length_drop]; simp; omega
    have hb_lt : r + 1 < (a.take i ++ [a.getD i 0 - 1, 1] ++ a.drop (i + 1)).length := by omega
    refine ⟨hb_lt, ?_⟩
    rw [List.drop_append, List.drop_append]
    have h1 : (a.take i).length = i := by rw [List.length_take]; omega
    have h2 : (a.take i ++ [a.getD i 0 - 1, 1]).length = i + 2 := by
      rw [List.length_append, h1]; simp
    rw [h1, h2]
    have hd1 : List.drop (r + 1) (a.take i) = [] := List.drop_eq_nil_of_le (by omega)
    rw [hd1, List.nil_append]
    have hd2 : List.drop (r + 1 - i) [a.getD i 0 - 1, 1] = [] := by
      apply List.drop_eq_nil_of_le; simp; omega
    rw [hd2, List.nil_append, List.drop_drop]
    congr 1
    omega
  · have hlen : (a.take (i - 1) ++ [a.getD (i - 1) 0 + 1] ++ a.drop (i + 1)).length = a.length - 1 := by
      rw [List.length_append, List.length_append, List.length_take, List.length_drop]; simp; omega
    have hb_lt : r - 1 < (a.take (i - 1) ++ [a.getD (i - 1) 0 + 1] ++ a.drop (i + 1)).length := by omega
    refine ⟨hb_lt, ?_⟩
    rw [List.drop_append, List.drop_append]
    have h1 : (a.take (i - 1)).length = i - 1 := by rw [List.length_take]; omega
    have h2 : (a.take (i - 1) ++ [a.getD (i - 1) 0 + 1]).length = i := by
      rw [List.length_append, h1]; simp; omega
    rw [h1, h2]
    have hd1 : List.drop (r - 1) (a.take (i - 1)) = [] := List.drop_eq_nil_of_le (by omega)
    rw [hd1, List.nil_append]
    have hd2 : List.drop (r - 1 - (i - 1)) [a.getD (i - 1) 0 + 1] = [] := by
      apply List.drop_eq_nil_of_le; simp; omega
    rw [hd2, List.nil_append, List.drop_drop]
    congr 1
    omega

theorem alpha_later_local_blocker_inherits_earlier_d_getD_eq_a (a : List ℕ) (i j : ℕ) (_hi : i < a.length) (hij : i < j) (hj : j < a.length)
    (he : i % 2 = 0) (hje : j % 2 = 0) (m : ℕ) (hm : m ≤ i) :
    (if 1 < a.getD j 0 then a.take j ++ [a.getD j 0 - 1, 1] ++ a.drop (j + 1)
     else a.take (j - 1) ++ [a.getD (j - 1) 0 + 1] ++ a.drop (j + 1)).getD m 0 = a.getD m 0 := by
  have hij2 : i + 2 ≤ j := by omega
  have hma : m < a.length := by omega
  split_ifs with hjc
  · have h1 : (a.take j).length = j := by rw [List.length_take]; omega
    rw [List.getD_append _ (a.drop (j + 1)) 0 m (by rw [List.length_append, h1]; simp; omega)]
    rw [List.getD_append (a.take j) _ 0 m (by omega)]
    rw [List.getD_eq_getElem _ 0 (by omega), List.getElem_take]
    exact (List.getD_eq_getElem a 0 hma).symm
  · have h1 : (a.take (j - 1)).length = j - 1 := by rw [List.length_take]; omega
    rw [List.getD_append _ (a.drop (j + 1)) 0 m (by rw [List.length_append, h1]; simp; omega)]
    rw [List.getD_append (a.take (j - 1)) _ 0 m (by omega)]
    rw [List.getD_eq_getElem _ 0 (by omega), List.getElem_take]
    exact (List.getD_eq_getElem a 0 hma).symm

theorem alpha_later_local_blocker_inherits_earlier_c_split_getD_eq_a (a : List ℕ) (i m : ℕ) (hi : i < a.length) (hm : m < i) :
    (a.take i ++ [a.getD i 0 - 1, 1] ++ a.drop (i + 1)).getD m 0 = a.getD m 0 := by
  have h1 : (a.take i).length = i := by rw [List.length_take]; omega
  rw [List.getD_append _ (a.drop (i + 1)) 0 m (by rw [List.length_append, h1]; simp; omega)]
  rw [List.getD_append (a.take i) _ 0 m (by omega)]
  rw [List.getD_eq_getElem _ 0 (by omega), List.getElem_take]
  exact (List.getD_eq_getElem a 0 (by omega)).symm

theorem alpha_later_local_blocker_inherits_earlier_c_conj_getD_eq_a (a : List ℕ) (i m : ℕ) (hi0 : 0 < i) (hi : i < a.length) (hm : m < i - 1) :
    (a.take (i - 1) ++ [a.getD (i - 1) 0 + 1] ++ a.drop (i + 1)).getD m 0 = a.getD m 0 := by
  have h1 : (a.take (i - 1)).length = i - 1 := by rw [List.length_take]; omega
  rw [List.getD_append _ (a.drop (i + 1)) 0 m (by rw [List.length_append, h1]; simp; omega)]
  rw [List.getD_append (a.take (i - 1)) _ 0 m (by omega)]
  rw [List.getD_eq_getElem _ 0 (by omega), List.getElem_take]
  exact (List.getD_eq_getElem a 0 (by omega)).symm

theorem alpha_later_local_blocker_inherits_earlier_c_split_getD_at_i (a : List ℕ) (i : ℕ) (hi : i < a.length) :
    (a.take i ++ [a.getD i 0 - 1, 1] ++ a.drop (i + 1)).getD i 0 = a.getD i 0 - 1 := by
  have h1 : (a.take i).length = i := by rw [List.length_take]; omega
  have h2 : (a.take i ++ [a.getD i 0 - 1, 1]).length = i + 2 := by
    rw [List.length_append, h1]; simp
  rw [List.getD_append _ (a.drop (i + 1)) 0 i (by omega)]
  rw [List.getD_append_right (a.take i) [a.getD i 0 - 1, 1] 0 i (by omega)]
  have : i - (a.take i).length = 0 := by omega
  rw [this]
  rfl

theorem alpha_later_local_blocker_inherits_earlier_c_conj_getD_at_sub (a : List ℕ) (i : ℕ) (hi0 : 0 < i) (hi : i < a.length) :
    (a.take (i - 1) ++ [a.getD (i - 1) 0 + 1] ++ a.drop (i + 1)).getD (i - 1) 0 = a.getD (i - 1) 0 + 1 := by
  have h1 : (a.take (i - 1)).length = i - 1 := by rw [List.length_take]; omega
  have h2 : (a.take (i - 1) ++ [a.getD (i - 1) 0 + 1]).length = i := by
    rw [List.length_append, h1]; simp; omega
  rw [List.getD_append _ (a.drop (i + 1)) 0 (i - 1) (by omega)]
  rw [List.getD_append_right (a.take (i - 1)) [a.getD (i - 1) 0 + 1] 0 (i - 1) (by omega)]
  have : i - 1 - (a.take (i - 1)).length = 0 := by omega
  rw [this]
  rfl

theorem alpha_later_local_blocker_inherits_earlier_c_lt_d (a : List ℕ) (i j : ℕ) (hi0 : 0 < i) (hi : i < a.length)
    (hij : i < j) (hj : j < a.length) (he : i % 2 = 0) (hje : j % 2 = 0) :
    let c := if 1 < a.getD i 0 then a.take i ++ [a.getD i 0 - 1, 1] ++ a.drop (i + 1)
             else a.take (i - 1) ++ [a.getD (i - 1) 0 + 1] ++ a.drop (i + 1)
    let d := if 1 < a.getD j 0 then a.take j ++ [a.getD j 0 - 1, 1] ++ a.drop (j + 1)
             else a.take (j - 1) ++ [a.getD (j - 1) 0 + 1] ++ a.drop (j + 1)
    alpha_lexical_lt c d := by
  intro c d
  have hd_eq : ∀ m ≤ i, d.getD m 0 = a.getD m 0 :=
    alpha_later_local_blocker_inherits_earlier_d_getD_eq_a a i j hi hij hj he hje
  by_cases hic : 1 < a.getD i 0
  · change alpha_lexical_lt c d
    have hc_def : c = a.take i ++ [a.getD i 0 - 1, 1] ++ a.drop (i + 1) := by
      change (if 1 < a.getD i 0 then _ else _) = _
      rw [if_pos hic]
    refine ⟨i, ?_, ?_, ?_⟩
    · have hclen : c.length = a.length + 1 := by
        rw [hc_def, List.length_append, List.length_append, List.length_take, List.length_drop]
        simp; omega
      have h1 : i < c.length := by rw [hclen]; omega
      exact lt_of_lt_of_le h1 (le_max_left c.length d.length)
    · intro m hm
      unfold alpha_signed_cell
      have : c.getD m 0 = a.getD m 0 := by
        rw [hc_def]
        exact alpha_later_local_blocker_inherits_earlier_c_split_getD_eq_a a i m hi hm
      rw [this, hd_eq m (by omega)]
    · unfold alpha_signed_cell
      rw [he, if_pos rfl, if_pos rfl]
      have : c.getD i 0 = a.getD i 0 - 1 := by
        rw [hc_def]
        exact alpha_later_local_blocker_inherits_earlier_c_split_getD_at_i a i hi
      rw [this, hd_eq i (by omega)]
      omega
  · change alpha_lexical_lt c d
    have hc_def : c = a.take (i - 1) ++ [a.getD (i - 1) 0 + 1] ++ a.drop (i + 1) := by
      change (if 1 < a.getD i 0 then _ else _) = _
      rw [if_neg hic]
    refine ⟨i - 1, ?_, ?_, ?_⟩
    · have hclen : c.length = a.length - 1 := by
        rw [hc_def, List.length_append, List.length_append, List.length_take, List.length_drop]
        simp; omega
      have h1 : i - 1 < c.length := by rw [hclen]; omega
      exact lt_of_lt_of_le h1 (le_max_left c.length d.length)
    · intro m hm
      unfold alpha_signed_cell
      have : c.getD m 0 = a.getD m 0 := by
        rw [hc_def]
        exact alpha_later_local_blocker_inherits_earlier_c_conj_getD_eq_a a i m hi0 hi hm
      rw [this, hd_eq m (by omega)]
    · unfold alpha_signed_cell
      have hne : ¬ (i - 1) % 2 = 0 := by omega
      rw [if_neg hne, if_neg hne]
      have : c.getD (i - 1) 0 = a.getD (i - 1) 0 + 1 := by
        rw [hc_def]
        exact alpha_later_local_blocker_inherits_earlier_c_conj_getD_at_sub a i hi0 hi
      rw [this, hd_eq (i - 1) (by omega)]
      omega

theorem alpha_later_local_blocker_inherits_earlier (a : List ℕ) (i j k : ℕ) (ha : alpha_is_lexical a) (hi0 : 0 < i) (hi : i < a.length) (he : i % 2 = 0) (hij : i < j) (hj : j < a.length) (hje : j % 2 = 0) : let c := if 1 < a.getD i 0 then a.take i ++ [a.getD i 0 - 1, 1] ++ a.drop (i + 1) else a.take (i - 1) ++ [a.getD (i - 1) 0 + 1] ++ a.drop (i + 1); let d := if 1 < a.getD j 0 then a.take j ++ [a.getD j 0 - 1, 1] ++ a.drop (j + 1) else a.take (j - 1) ++ [a.getD (j - 1) 0 + 1] ++ a.drop (j + 1); let bound := if 1 < a.getD j 0 then j + 1 else j - 1; (∀ s : ℕ, 0 < s → s < d.length → s ≤ bound → alpha_lexical_lt (d.drop s) d) → 0 < k → k < d.length → ¬ alpha_lexical_lt (d.drop k) d → let r := if 1 < a.getD j 0 then k - 1 else k + 1; let b := if 1 < a.getD i 0 then r + 1 else r - 1; j < r ∧ b < c.length ∧ b % 2 = k % 2 ∧ ¬ alpha_lexical_lt (c.drop b) c := by
  intro c d bound hearly hk0 hklen hblock r b
  have hj0 : 0 < j := by omega
  have hbound : bound < k := by
    by_contra! hle
    exact hblock (hearly k hk0 hklen hle)
  have hd_res := alpha_later_local_blocker_inherits_earlier_drop_d_eq_a a j k hj0 hj hklen hbound
  rcases hd_res with ⟨hjr, hr_len, hdrop_d⟩
  have hir : i + 1 < r := by omega
  have hc_res := alpha_later_local_blocker_inherits_earlier_drop_c_eq_a a i r hi0 hi hir hr_len
  rcases hc_res with ⟨hb_len, hdrop_c⟩
  have hk_ge2 : 2 ≤ k := by
    dsimp [bound] at hbound
    split_ifs at hbound with hjc <;> omega
  have hparity : b % 2 = k % 2 := by
    dsimp [r, b]
    split_ifs <;> omega
  refine ⟨hjr, hb_len, hparity, ?_⟩
  intro hcb
  have hcd : alpha_lexical_lt c d :=
    alpha_later_local_blocker_inherits_earlier_c_lt_d a i j hi0 hi hij hj he hje
  have hdrop_eq : c.drop b = d.drop k := by
    rw [hdrop_c, hdrop_d]
  have hdk_lt_c : alpha_lexical_lt (d.drop k) c := by
    rwa [← hdrop_eq]
  have hdk_lt_d : alpha_lexical_lt (d.drop k) d :=
    alpha_later_local_blocker_inherits_earlier_lexical_lt_trans (d.drop k) c d hdk_lt_c hcd
  exact hblock hdk_lt_d
