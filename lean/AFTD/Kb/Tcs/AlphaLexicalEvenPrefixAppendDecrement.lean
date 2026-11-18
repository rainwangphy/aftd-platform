import AFTD.Prelude
import AFTD.Kb.Tcs.AlphaIsLexical
import AFTD.Kb.Tcs.AlphaLexicalLt
import AFTD.Kb.Tcs.AlphaSignedCell
import AFTD.Kb.Tcs.AlphaLexicalFirstNegativeStepExists
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# alpha_lexical_even_prefix_append_decrement

Topic: combinatorics   Node: 6994c7f3920f

Provenance: helper lemma. Even-split factorization helper for OP-392, arXiv:2610.24758; alternating order and extensions as in arXiv:0810.5205.

For a lexical sequence with an even-length nonempty lexical prefix and a following cell greater than one, appending one less than that cell to the prefix produces a lexical sequence.
-/

theorem alpha_pdec_signed_zero (A : List ℕ) (j : ℕ) (h : A.length ≤ j) :
    alpha_signed_cell A j = 0 := by
  unfold alpha_signed_cell
  rw [List.getD_eq_default _ _ h]; split_ifs <;> simp

theorem alpha_pdec_signed_le (A B : List ℕ) (L : ℕ) (hlt : alpha_lexical_lt A B)
    (heq : ∀ j < L, alpha_signed_cell A j = alpha_signed_cell B j) :
    alpha_signed_cell A L ≤ alpha_signed_cell B L := by
  obtain ⟨r, _, hpre, hr⟩ := hlt
  rcases lt_trichotomy r L with h | h | h
  · exact absurd (heq r h) (ne_of_lt hr)
  · exact h ▸ hr.le
  · exact (hpre L h).le

theorem alpha_pdec_signed_eq_iff (A B : List ℕ) (j : ℕ) :
    alpha_signed_cell A j = alpha_signed_cell B j ↔ A.getD j 0 = B.getD j 0 := by
  unfold alpha_signed_cell
  split_ifs <;> omega

theorem alpha_pdec_signed_even (A : List ℕ) (j : ℕ) (h : j % 2 = 0) :
    alpha_signed_cell A j = (A.getD j 0 : ℤ) := by
  unfold alpha_signed_cell; rw [if_pos h]

theorem alpha_pdec_getD_take (a : List ℕ) (i j : ℕ) (hj : j < i) :
    (a.take i).getD j 0 = a.getD j 0 := by
  simp [List.getD_eq_getElem?_getD, hj]

theorem alpha_pdec_getD_drop (a : List ℕ) (k j : ℕ) :
    (a.drop k).getD j 0 = a.getD (k + j) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem alpha_pdec_getD_append_left (u X : List ℕ) (j : ℕ) (hj : j < u.length) :
    (u ++ X).getD j 0 = u.getD j 0 := List.getD_append _ _ _ _ hj

theorem alpha_lexical_even_prefix_append_decrement (a : List ℕ) (i : ℕ) (ha : alpha_is_lexical a) (hi0 : 0 < i) (hi : i < a.length) (he : i % 2 = 0) (hc : 1 < a.getD i 0) (hp : alpha_is_lexical (a.take i)) : alpha_is_lexical (a.take i ++ [a.getD i 0 - 1]) := by
  obtain ⟨_, hpos, hlex⟩ := ha
  obtain ⟨_, _, hplex⟩ := hp
  have hpl : (a.take i).length = i := by simp; omega
  -- cells of f
  have hfj : ∀ j < i, (a.take i ++ [a.getD i 0 - 1]).getD j 0 = a.getD j 0 := by
    intro j hj
    rw [alpha_pdec_getD_append_left _ _ _ (by omega), alpha_pdec_getD_take _ _ _ hj]
  have hfi : (a.take i ++ [a.getD i 0 - 1]).getD i 0 = a.getD i 0 - 1 := by
    rw [List.getD_append_right _ _ _ _ (by omega)]; simp [hpl]
  refine ⟨by simp, ?_, ?_⟩
  · intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact hpos v (List.mem_of_mem_take hv)
    · rw [List.mem_singleton] at hv; subst hv; omega
  · intro k hk hk0
    simp only [List.length_append, hpl, List.length_singleton] at hk
    have hdrop : (a.take i ++ [a.getD i 0 - 1]).drop k =
        (a.take i).drop k ++ [a.getD i 0 - 1] := List.drop_append_of_le_length (by omega)
    set D := (a.take i).drop k with hD
    have hDl : D.length = i - k := by simp [hD, hpl]
    have hDg : ∀ j, k + j < i → D.getD j 0 = a.getD (k + j) 0 := by
      intro j hj; rw [hD, alpha_pdec_getD_drop, alpha_pdec_getD_take _ _ _ hj]
    rw [hdrop]
    -- a's suffix at k agrees with D ++ a.drop i
    have hak : ∀ j, (a.drop k).getD j 0 = a.getD (k + j) 0 := alpha_pdec_getD_drop a k
    have hLk := hlex k (by omega) hk0
    by_cases hki : k = i
    · subst hki
      -- compare [x] with f at cell 0
      have h0 := alpha_pdec_signed_le _ _ 0 hLk (by intro j hj; omega)
      have ha0 : (a.drop k).getD 0 0 = a.getD k 0 := by rw [hak, Nat.add_zero]
      rw [alpha_pdec_signed_even _ _ (by norm_num), alpha_pdec_signed_even _ _ (by norm_num),
        ha0] at h0
      have h0' : a.getD k 0 ≤ a.getD 0 0 := by exact_mod_cast h0
      refine ⟨0, by simp, by intro j hj; omega, ?_⟩
      have hD0 : D = [] := by rw [← List.length_eq_zero_iff, hDl]; simp
      rw [alpha_pdec_signed_even _ _ (by norm_num), alpha_pdec_signed_even _ _ (by norm_num),
        hfj 0 hi0, hD0]
      simp only [List.nil_append, List.getD_cons_zero]
      have : a.getD k 0 - 1 < a.getD 0 0 := by omega
      exact_mod_cast this
    · have hki' : k < i := by omega
      obtain ⟨q, _, hpre, hq⟩ := hplex k (by omega) hk0
      by_cases hqL : q < i - k
      · refine ⟨q, by simp; omega, ?_, ?_⟩
        · intro j hj
          have := hpre j hj
          rw [alpha_pdec_signed_eq_iff] at this ⊢
          rw [alpha_pdec_getD_append_left _ _ _ (by omega),
            alpha_pdec_getD_append_left _ _ _ (by omega)]
          exact this
        · have e1 : ∀ B : List ℕ, alpha_signed_cell (D ++ B) q = alpha_signed_cell D q := by
            intro B; unfold alpha_signed_cell
            rw [alpha_pdec_getD_append_left _ _ _ (by omega)]
          have e2 : ∀ B : List ℕ, alpha_signed_cell (a.take i ++ B) q =
              alpha_signed_cell (a.take i) q := by
            intro B; unfold alpha_signed_cell
            rw [alpha_pdec_getD_append_left _ _ _ (by omega)]
          rw [e1, e2]; exact hq
      · -- D is a proper prefix of the prefix; the decisive cell is L = i - k
        have hDlq : D.length ≤ q := by rw [hDl]; omega
        have hDz : alpha_signed_cell D q = 0 := alpha_pdec_signed_zero _ _ hDlq
        have hqi : q < i := by
          by_contra hcon
          have : alpha_signed_cell (a.take i) q = 0 :=
            alpha_pdec_signed_zero _ _ (by rw [hpl]; omega)
          rw [hDz, this] at hq; exact lt_irrefl _ hq
        have hpq : 0 < a.getD q 0 := by
          rw [List.getD_eq_getElem _ _ (by omega)]
          exact hpos _ (List.getElem_mem _)
        have hqeq : q = i - k := by
          by_contra hne
          have hL := hpre (i - k) (by omega)
          rw [alpha_pdec_signed_eq_iff, alpha_pdec_getD_take _ _ _ (by omega),
            List.getD_eq_default _ _ (le_of_eq hDl)] at hL
          have : 0 < a.getD (i - k) 0 := by
            rw [List.getD_eq_getElem _ _ (by omega)]
            exact hpos _ (List.getElem_mem _)
          omega
        subst hqeq
        have heven : (i - k) % 2 = 0 := by
          rw [hDz] at hq
          unfold alpha_signed_cell at hq
          split_ifs at hq with hh
          · exact hh
          · omega
        -- a_i ≤ a_{i-k} from lexicality of a
        have hagree : ∀ j < i - k, alpha_signed_cell (a.drop k) j = alpha_signed_cell a j := by
          intro j hj
          have := hpre j hj
          rw [alpha_pdec_signed_eq_iff] at this ⊢
          rw [hak, ← hDg j (by omega), this, alpha_pdec_getD_take _ _ _ (by omega)]
        have hle := alpha_pdec_signed_le _ _ (i - k) hLk hagree
        have hik : k + (i - k) = i := by omega
        simp only [alpha_signed_cell, heven, if_true, hak, hik] at hle
        refine ⟨i - k, by simp; omega, ?_, ?_⟩
        · intro j hj
          have := hpre j hj
          rw [alpha_pdec_signed_eq_iff] at this ⊢
          rw [alpha_pdec_getD_append_left _ _ _ (by omega), this, hfj j (by omega),
            alpha_pdec_getD_take _ _ _ (by omega)]
        · have g1 : (D ++ [a.getD i 0 - 1]).getD (i - k) 0 = a.getD i 0 - 1 := by
            rw [List.getD_append_right _ _ _ _ (by omega)]; simp [hDl]
          simp only [alpha_signed_cell, heven, if_true, g1, hfj (i - k) (by omega)]
          omega
