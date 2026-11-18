import AFTD.Prelude
import AFTD.Kb.Tcs.AlphaIsLexical
import AFTD.Kb.Tcs.AlphaLexicalLt
import AFTD.Kb.Tcs.AlphaLexicalFirstNegativeStepExists
import AFTD.Kb.Tcs.AlphaLexicalOddCompletionIffRotationMaxOfPrime
import AFTD.Kb.Tcs.AlphaSignedCell

/-!
# alpha_even_split_early_suffix_lt_of_lexical_prefix

Topic: combinatorics   Node: cb9eb5e52799

Provenance: helper lemma. Structural helper for the lexical route to OP-392, arXiv:2610.24758; see arXiv:0810.5205 for the alternating order and elementary split.

Let a be lexical, and let its even-length nonempty prefix ending immediately before a cell greater than one also be lexical. After splitting that cell, every proper suffix starting at or before the inserted one is strictly below the resulting sequence in alternating order.
-/

private def alpha_even_split_early_suffix_lt_of_lexical_prefix_ec (a : List ℕ) (i : ℕ) : List ℕ :=
  a.take i ++ [a.getD i 0 - 1, 1] ++ a.drop (i + 1)

private lemma alpha_even_split_early_suffix_lt_of_lexical_prefix_signed_eq {a b : List ℕ} {i : ℕ}
    (h : a.getD i 0 = b.getD i 0) : alpha_signed_cell a i = alpha_signed_cell b i := by
  unfold alpha_signed_cell
  rw [h]

private lemma alpha_even_split_early_suffix_lt_of_lexical_prefix_not_lt_of_first_difference
    (L M : List ℕ) (i : ℕ)
    (h : ∀ j < i, alpha_signed_cell L j = alpha_signed_cell M j)
    (hlt : alpha_signed_cell M i < alpha_signed_cell L i) :
    ¬ alpha_lexical_lt L M := by
  intro hLM
  rcases hLM with ⟨m, hm, hmeq, hmlt⟩
  rcases lt_trichotomy m i with hmi | hmi | hmi
  · have := h m hmi
    rw [this] at hmlt
    exact lt_irrefl _ hmlt
  · subst hmi
    exact (lt_asymm hmlt) hlt
  · have := hmeq i hmi
    rw [this] at hlt
    exact lt_irrefl _ hlt

private lemma alpha_even_split_early_suffix_lt_of_lexical_prefix_ec_getD_left (a : List ℕ) (i j : ℕ)
    (hi : i < a.length) (hj : j < i) :
    (alpha_even_split_early_suffix_lt_of_lexical_prefix_ec a i).getD j 0 = a.getD j 0 := by
  unfold alpha_even_split_early_suffix_lt_of_lexical_prefix_ec
  have hL1 : (a.take i ++ [a.getD i 0 - 1, 1]).length = i + 2 := by
    simp only [List.length_append, List.length_cons, List.length_nil, List.length_take]; omega
  rw [alpha_rot_getD_left (a.take i ++ [a.getD i 0 - 1, 1]) (a.drop (i + 1)) j (by omega)]
  rw [alpha_rot_getD_left (a.take i) [a.getD i 0 - 1, 1] j (by
    rw [List.length_take]; omega)]
  exact alpha_rot_getD_take a i j hj

private lemma alpha_even_split_early_suffix_lt_of_lexical_prefix_ec_getD_i (a : List ℕ) (i : ℕ)
    (hi : i < a.length) :
    (alpha_even_split_early_suffix_lt_of_lexical_prefix_ec a i).getD i 0 = a.getD i 0 - 1 := by
  unfold alpha_even_split_early_suffix_lt_of_lexical_prefix_ec
  have hL1 : (a.take i ++ [a.getD i 0 - 1, 1]).length = i + 2 := by
    simp only [List.length_append, List.length_cons, List.length_nil, List.length_take]; omega
  rw [alpha_rot_getD_left (a.take i ++ [a.getD i 0 - 1, 1]) (a.drop (i + 1)) i (by omega)]
  rw [alpha_rot_getD_right (a.take i) [a.getD i 0 - 1, 1] i (by
    rw [List.length_take]; omega)]
  have h0 : i - (a.take i).length = 0 := by rw [List.length_take]; omega
  rw [h0]
  rfl

private lemma alpha_even_split_early_suffix_lt_of_lexical_prefix_ec_getD_i_succ (a : List ℕ) (i : ℕ)
    (hi : i < a.length) :
    (alpha_even_split_early_suffix_lt_of_lexical_prefix_ec a i).getD (i + 1) 0 = 1 := by
  unfold alpha_even_split_early_suffix_lt_of_lexical_prefix_ec
  have hL1 : (a.take i ++ [a.getD i 0 - 1, 1]).length = i + 2 := by
    simp only [List.length_append, List.length_cons, List.length_nil, List.length_take]; omega
  rw [alpha_rot_getD_left (a.take i ++ [a.getD i 0 - 1, 1]) (a.drop (i + 1)) (i + 1) (by omega)]
  rw [alpha_rot_getD_right (a.take i) [a.getD i 0 - 1, 1] (i + 1) (by
    rw [List.length_take]; omega)]
  have h1 : i + 1 - (a.take i).length = 1 := by rw [List.length_take]; omega
  rw [h1]
  rfl

private lemma alpha_even_split_early_suffix_lt_of_lexical_prefix_not_lexical_take_of_period
    (a : List ℕ) (i k d : ℕ) (hi : i < a.length) (hk : 0 < k) (hki : k < i)
    (hd : d = i - k) (hdo : d % 2 = 1)
    (hagree : ∀ j < d, a.getD (k + j) 0 = a.getD j 0)
    (hpos : 0 < a.getD d 0) :
    ¬ alpha_is_lexical (a.take i) := by
  intro hb
  have hlen : (a.take i).length = i := by rw [List.length_take]; omega
  have hkle : k < (a.take i).length := by rw [hlen]; exact hki
  have hlex : alpha_lexical_lt ((a.take i).drop k) (a.take i) := hb.2.2 k hkle hk
  have hlt : alpha_signed_cell (a.take i) d < alpha_signed_cell ((a.take i).drop k) d := by
    have hdrop : ((a.take i).drop k).getD d 0 = 0 := by
      rw [alpha_lexical_first_negative_step_exists_getD_drop]
      apply List.getD_eq_default
      rw [hlen]; omega
    have hbpos : 0 < (a.take i).getD d 0 := by
      rw [alpha_rot_getD_take a i d (by omega)]
      exact hpos
    unfold alpha_signed_cell
    rw [if_neg (by omega : ¬ d % 2 = 0), if_neg (by omega : ¬ d % 2 = 0), hdrop]
    have hcast : (0:ℤ) < ((a.take i).getD d 0 : ℤ) := by exact_mod_cast hbpos
    omega
  have heq : ∀ j < d, alpha_signed_cell ((a.take i).drop k) j = alpha_signed_cell (a.take i) j := by
    intro j hj
    apply alpha_even_split_early_suffix_lt_of_lexical_prefix_signed_eq
    rw [alpha_lexical_first_negative_step_exists_getD_drop]
    rw [alpha_rot_getD_take a i (k+j) (by omega), alpha_rot_getD_take a i j (by omega)]
    exact hagree j hj
  exact (alpha_even_split_early_suffix_lt_of_lexical_prefix_not_lt_of_first_difference
    ((a.take i).drop k) (a.take i) d heq hlt) hlex

theorem alpha_even_split_early_suffix_lt_of_lexical_prefix (a : List ℕ) (i : ℕ) (ha : alpha_is_lexical a) (hi0 : 0 < i) (hi : i < a.length) (he : i % 2 = 0) (hc : 1 < a.getD i 0) (hp : alpha_is_lexical (a.take i)) : let c := a.take i ++ [a.getD i 0 - 1, 1] ++ a.drop (i + 1); ∀ k : ℕ, 0 < k → k < c.length → k ≤ i + 1 → alpha_lexical_lt (c.drop k) c := by
  dsimp only
  intro k hk0 hklen hkle
  change alpha_lexical_lt ((alpha_even_split_early_suffix_lt_of_lexical_prefix_ec a i).drop k)
    (alpha_even_split_early_suffix_lt_of_lexical_prefix_ec a i)
  have hpos_i : 0 < a.getD i 0 := alpha_lexical_first_negative_step_exists_cell_pos a ha i hi
  have hle_i : a.getD i 0 ≤ a.getD 0 0 := alpha_lexical_first_negative_step_exists_cell_le_first a ha i hi
  rcases lt_or_ge k (i + 1) with hk_lt' | hk_ge'
  · rcases eq_or_lt_of_le (show k ≤ i by omega) with hk_eq_i | hk_lt_i
    · subst k
      apply alpha_rot_cl_of _ _ 0
      · intro j hj; omega
      · left
        refine ⟨by norm_num, ?_⟩
        rw [alpha_lexical_first_negative_step_exists_getD_drop_zero,
            alpha_even_split_early_suffix_lt_of_lexical_prefix_ec_getD_i a i hi,
            alpha_even_split_early_suffix_lt_of_lexical_prefix_ec_getD_left a i 0 hi hi0]
        omega
    · set d := i - k with hd
      have hdk : k + d = i := by omega
      have hdi : d < i := by omega
      have hka : k < a.length := by omega
      have hlex : alpha_lexical_lt (a.drop k) a := ha.2.2 k hka hk0
      rcases alpha_rot_cl_to (a.drop k) a hlex with ⟨m, hmeq, hmcase⟩
      have hagree : ∀ j < m, a.getD (k + j) 0 = a.getD j 0 := by
        intro j hj
        rw [← alpha_lexical_first_negative_step_exists_getD_drop]
        exact hmeq j hj
      have hmcase' : (m % 2 = 0 ∧ a.getD (k+m) 0 < a.getD m 0) ∨
                     (m % 2 = 1 ∧ a.getD m 0 < a.getD (k+m) 0) := by
        rcases hmcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left; exact ⟨h1, by rwa [alpha_lexical_first_negative_step_exists_getD_drop] at h2⟩
        · right; exact ⟨h1, by rwa [alpha_lexical_first_negative_step_exists_getD_drop] at h2⟩
      rcases lt_trichotomy m d with hmd | hmd | hmd
      · -- m < d
        apply alpha_rot_cl_of ((alpha_even_split_early_suffix_lt_of_lexical_prefix_ec a i).drop k)
          (alpha_even_split_early_suffix_lt_of_lexical_prefix_ec a i) m
        · intro j hj
          rw [alpha_lexical_first_negative_step_exists_getD_drop,
              alpha_even_split_early_suffix_lt_of_lexical_prefix_ec_getD_left a i (k+j) hi (by omega),
              alpha_even_split_early_suffix_lt_of_lexical_prefix_ec_getD_left a i j hi (by omega)]
          exact hagree j hj
        · have hLm : ((alpha_even_split_early_suffix_lt_of_lexical_prefix_ec a i).drop k).getD m 0
              = a.getD (k+m) 0 := by
            rw [alpha_lexical_first_negative_step_exists_getD_drop,
                alpha_even_split_early_suffix_lt_of_lexical_prefix_ec_getD_left a i (k+m) hi (by omega)]
          have hMm : (alpha_even_split_early_suffix_lt_of_lexical_prefix_ec a i).getD m 0
              = a.getD m 0 :=
            alpha_even_split_early_suffix_lt_of_lexical_prefix_ec_getD_left a i m hi (by omega)
          rcases hmcase' with ⟨h1,h2⟩ | ⟨h1,h2⟩
          · left; exact ⟨h1, by rw [hLm, hMm]; exact h2⟩
          · right; exact ⟨h1, by rw [hLm, hMm]; exact h2⟩
      · -- m = d
        rw [hmd] at hmcase'
        have hLd : ((alpha_even_split_early_suffix_lt_of_lexical_prefix_ec a i).drop k).getD d 0
            = a.getD i 0 - 1 := by
          rw [alpha_lexical_first_negative_step_exists_getD_drop, hdk,
              alpha_even_split_early_suffix_lt_of_lexical_prefix_ec_getD_i a i hi]
        have hMd : (alpha_even_split_early_suffix_lt_of_lexical_prefix_ec a i).getD d 0
            = a.getD d 0 :=
          alpha_even_split_early_suffix_lt_of_lexical_prefix_ec_getD_left a i d hi hdi
        have heq_d : ∀ j < d, ((alpha_even_split_early_suffix_lt_of_lexical_prefix_ec a i).drop k).getD j 0
            = (alpha_even_split_early_suffix_lt_of_lexical_prefix_ec a i).getD j 0 := by
          intro j hj
          rw [alpha_lexical_first_negative_step_exists_getD_drop,
              alpha_even_split_early_suffix_lt_of_lexical_prefix_ec_getD_left a i (k+j) hi (by omega),
              alpha_even_split_early_suffix_lt_of_lexical_prefix_ec_getD_left a i j hi (by omega)]
          exact hagree j (by omega)
        rcases hmcase' with ⟨h1,h2⟩ | ⟨h1,h2⟩
        · apply alpha_rot_cl_of ((alpha_even_split_early_suffix_lt_of_lexical_prefix_ec a i).drop k)
            (alpha_even_split_early_suffix_lt_of_lexical_prefix_ec a i) d
          · exact heq_d
          · left
            refine ⟨h1, ?_⟩
            rw [hLd, hMd]
            rw [hdk] at h2
            omega
        · by_cases hlt : a.getD d 0 < a.getD i 0 - 1
          · apply alpha_rot_cl_of ((alpha_even_split_early_suffix_lt_of_lexical_prefix_ec a i).drop k)
              (alpha_even_split_early_suffix_lt_of_lexical_prefix_ec a i) d
            · exact heq_d
            · right
              refine ⟨h1, ?_⟩
              rw [hLd, hMd]; exact hlt
          · exfalso
            refine (alpha_even_split_early_suffix_lt_of_lexical_prefix_not_lexical_take_of_period
              a i k d hi hk0 hk_lt_i hd h1 ?_ ?_) hp
            · intro j hj
              exact hagree j (by omega)
            · rw [hdk] at h2; omega
      · -- d < m
        have hLd : ((alpha_even_split_early_suffix_lt_of_lexical_prefix_ec a i).drop k).getD d 0
            = a.getD i 0 - 1 := by
          rw [alpha_lexical_first_negative_step_exists_getD_drop, hdk,
              alpha_even_split_early_suffix_lt_of_lexical_prefix_ec_getD_i a i hi]
        have hMd : (alpha_even_split_early_suffix_lt_of_lexical_prefix_ec a i).getD d 0
            = a.getD d 0 :=
          alpha_even_split_early_suffix_lt_of_lexical_prefix_ec_getD_left a i d hi hdi
        have heq_d : ∀ j < d, ((alpha_even_split_early_suffix_lt_of_lexical_prefix_ec a i).drop k).getD j 0
            = (alpha_even_split_early_suffix_lt_of_lexical_prefix_ec a i).getD j 0 := by
          intro j hj
          rw [alpha_lexical_first_negative_step_exists_getD_drop,
              alpha_even_split_early_suffix_lt_of_lexical_prefix_ec_getD_left a i (k+j) hi (by omega),
              alpha_even_split_early_suffix_lt_of_lexical_prefix_ec_getD_left a i j hi (by omega)]
          exact hagree j (by omega)
        have hmeq_d : a.getD i 0 = a.getD d 0 := by
          have hh := hmeq d (by omega)
          rw [alpha_lexical_first_negative_step_exists_getD_drop, hdk] at hh
          exact hh
        by_cases hpar : d % 2 = 0
        · apply alpha_rot_cl_of ((alpha_even_split_early_suffix_lt_of_lexical_prefix_ec a i).drop k)
            (alpha_even_split_early_suffix_lt_of_lexical_prefix_ec a i) d
          · exact heq_d
          · left
            refine ⟨hpar, ?_⟩
            rw [hLd, hMd]; omega
        · have hd1 : d % 2 = 1 := by omega
          exfalso
          refine (alpha_even_split_early_suffix_lt_of_lexical_prefix_not_lexical_take_of_period
            a i k d hi hk0 hk_lt_i hd hd1 ?_ ?_) hp
          · intro j hj
            have hh := hmeq j (by omega)
            rw [alpha_lexical_first_negative_step_exists_getD_drop] at hh
            exact hh
          · rw [← hmeq_d]; exact hpos_i
  · have hk_eq : k = i + 1 := by omega
    subst k
    apply alpha_rot_cl_of _ _ 0
    · intro j hj; omega
    · left
      refine ⟨by norm_num, ?_⟩
      rw [alpha_lexical_first_negative_step_exists_getD_drop_zero,
          alpha_even_split_early_suffix_lt_of_lexical_prefix_ec_getD_i_succ a i hi,
          alpha_even_split_early_suffix_lt_of_lexical_prefix_ec_getD_left a i 0 hi hi0]
      omega
