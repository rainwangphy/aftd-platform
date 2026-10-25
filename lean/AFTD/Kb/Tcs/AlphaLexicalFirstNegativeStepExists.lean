import AFTD.Prelude
import AFTD.Kb.Tcs.AlphaIsLexical
import AFTD.Kb.Tcs.AlphaElementaryCellStep
import AFTD.Kb.Tcs.AlphaLexicalLt
import AFTD.Kb.Tcs.AlphaSignedCell
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# alpha_lexical_first_negative_step_exists

Topic: combinatorics   Node: 6d19e4d59bc7

Provenance: helper lemma. Run-length helpers for OP-392, arXiv:2610.24758, Conjecture 1; lexical sequences and elementary operations from arXiv:0810.5205, Definitions 1.1, Section 2, Theorem 3.1 and Corollary 3.3. No new research advance is claimed for these supporting statements.

A lexical sequence with at least two cells has an elementary lexical successor at its first negative cell.
-/

lemma alpha_lexical_first_negative_step_exists_signed_cell_eq_zero_of_ge
    (a : List ℕ) (i : ℕ) (hi : a.length ≤ i) :
    alpha_signed_cell a i = 0 := by
  dsimp [alpha_signed_cell]
  rw [List.getD_eq_default _ _ hi]
  split <;> rfl

lemma alpha_lexical_first_negative_step_exists_lt_max_of_signed_cell_lt
    (x z : List ℕ) (i : ℕ)
    (hlt : alpha_signed_cell x i < alpha_signed_cell z i) :
    i < max x.length z.length := by
  by_contra! hge
  have hx : x.length ≤ i := le_of_max_le_left hge
  have hz : z.length ≤ i := le_of_max_le_right hge
  rw [alpha_lexical_first_negative_step_exists_signed_cell_eq_zero_of_ge x i hx,
      alpha_lexical_first_negative_step_exists_signed_cell_eq_zero_of_ge z i hz] at hlt
  omega

theorem alpha_lexical_first_negative_step_exists_lt_trans (x y z : List ℕ)
    (hxy : alpha_lexical_lt x y) (hyz : alpha_lexical_lt y z) :
    alpha_lexical_lt x z := by
  rcases hxy with ⟨i, hi, hxy_eq, hxy_lt⟩
  rcases hyz with ⟨k, hk, hyz_eq, hyz_lt⟩
  rcases lt_trichotomy i k with h | rfl | h
  · refine ⟨i, alpha_lexical_first_negative_step_exists_lt_max_of_signed_cell_lt x z i ?_, fun j hj => ?_, ?_⟩
    · rw [← hyz_eq i h]; exact hxy_lt
    · rw [hxy_eq j hj, hyz_eq j (lt_trans hj h)]
    · rw [← hyz_eq i h]; exact hxy_lt
  · refine ⟨i, alpha_lexical_first_negative_step_exists_lt_max_of_signed_cell_lt x z i ?_, fun j hj => ?_, ?_⟩
    · exact lt_trans hxy_lt hyz_lt
    · rw [hxy_eq j hj, hyz_eq j hj]
    · exact lt_trans hxy_lt hyz_lt
  · refine ⟨k, alpha_lexical_first_negative_step_exists_lt_max_of_signed_cell_lt x z k ?_, fun j hj => ?_, ?_⟩
    · rw [hxy_eq k h]; exact hyz_lt
    · rw [hxy_eq j (lt_trans hj h), hyz_eq j hj]
    · rw [hxy_eq k h]; exact hyz_lt

lemma alpha_lexical_first_negative_step_exists_getD_drop (a : List ℕ) (k j : ℕ) :
    (a.drop k).getD j 0 = a.getD (k + j) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]

lemma alpha_lexical_first_negative_step_exists_getD_drop_zero (a : List ℕ) (k : ℕ) :
    (a.drop k).getD 0 0 = a.getD k 0 := by
  rw [alpha_lexical_first_negative_step_exists_getD_drop, add_zero]

lemma alpha_lexical_first_negative_step_exists_cell_le_first (a : List ℕ) (ha : alpha_is_lexical a)
    (k : ℕ) (hk : k < a.length) :
    a.getD k 0 ≤ a.getD 0 0 := by
  rcases eq_or_lt_of_le (Nat.zero_le k) with rfl | hk0
  · rfl
  · have hlt := ha.2.2 k hk hk0
    rcases hlt with ⟨i, hi, heq, hlt⟩
    dsimp [alpha_signed_cell] at heq hlt
    rcases eq_or_lt_of_le (Nat.zero_le i) with rfl | hi0
    · rw [alpha_lexical_first_negative_step_exists_getD_drop_zero] at hlt; omega
    · have h0 := heq 0 hi0
      rw [alpha_lexical_first_negative_step_exists_getD_drop_zero] at h0; omega

lemma alpha_lexical_first_negative_step_exists_cell_pos (a : List ℕ) (ha : alpha_is_lexical a)
    (k : ℕ) (hk : k < a.length) :
    0 < a.getD k 0 := by
  rw [List.getD_eq_getElem a 0 hk]
  exact ha.2.1 _ (List.getElem_mem hk)

lemma alpha_lexical_first_negative_step_exists_two_le_first (a : List ℕ) (ha : alpha_is_lexical a)
    (hlen : 2 ≤ a.length) :
    2 ≤ a.getD 0 0 := by
  by_contra! hlt
  have hpos0 : 0 < a.getD 0 0 := alpha_lexical_first_negative_step_exists_cell_pos a ha 0 (by omega)
  have ha0 : a.getD 0 0 = 1 := by omega
  let k := a.length - 1
  have hk : k < a.length := by omega
  have hk0 : 0 < k := by omega
  have hdrop_lt := ha.2.2 k hk hk0
  rcases hdrop_lt with ⟨i, hi, heq, hlt_i⟩
  have hpos1 : 0 < a.getD 1 0 := alpha_lexical_first_negative_step_exists_cell_pos a ha 1 (by omega)
  have hle1 : a.getD 1 0 ≤ a.getD 0 0 := alpha_lexical_first_negative_step_exists_cell_le_first a ha 1 (by omega)
  have ha1 : a.getD 1 0 = 1 := by omega
  have hdrop_1 : alpha_signed_cell (a.drop k) 1 = 0 := by
    dsimp [alpha_signed_cell]
    rw [List.getD_eq_default _ _ (by rw [List.length_drop]; omega)]
    rfl
  have ha_1 : alpha_signed_cell a 1 = -1 := by
    dsimp [alpha_signed_cell]; rw [ha1]; rfl
  rcases eq_or_lt_of_le (Nat.zero_le i) with rfl | hi0
  · dsimp [alpha_signed_cell] at hlt_i
    rw [alpha_lexical_first_negative_step_exists_getD_drop_zero, ha0] at hlt_i
    have : 0 < a.getD k 0 := alpha_lexical_first_negative_step_exists_cell_pos a ha k hk
    omega
  · rcases eq_or_lt_of_le (show 1 ≤ i by omega) with rfl | hi1
    · rw [hdrop_1, ha_1] at hlt_i; omega
    · have h1 := heq 1 hi1
      rw [hdrop_1, ha_1] at h1; omega

lemma alpha_lexical_first_negative_step_exists_lt_of_first_cell_lt (x y : List ℕ)
    (hlt : x.getD 0 0 < y.getD 0 0) (hlen : 0 < max x.length y.length) :
    alpha_lexical_lt x y := by
  refine ⟨0, hlen, fun j hj => by omega, ?_⟩
  dsimp [alpha_signed_cell]; omega

lemma alpha_lexical_first_negative_step_exists_lt_of_second_cell_gt (x y : List ℕ)
    (h0 : x.getD 0 0 = y.getD 0 0) (h1 : y.getD 1 0 < x.getD 1 0)
    (hlen : 1 < max x.length y.length) :
    alpha_lexical_lt x y := by
  refine ⟨1, hlen, fun j hj => ?_, ?_⟩
  · have : j = 0 := by omega
    subst this
    dsimp [alpha_signed_cell]; omega
  · dsimp [alpha_signed_cell]; omega

lemma alpha_lexical_first_negative_step_exists_getD_cons_append (x : ℕ) (l : List ℕ) (k : ℕ) (hk : 0 < k) :
    ([x] ++ l).getD k 0 = l.getD (k - 1) 0 := by
  rcases k with _ | k
  · contradiction
  · rfl

lemma alpha_lexical_first_negative_step_exists_drop_ge_three (a : List ℕ) (a1 : ℕ) (k : ℕ) (hk : 3 ≤ k) :
    (([a.getD 0 0, a1 - 1, 1] ++ a.drop 2).drop k) = a.drop (k - 1) := by
  rcases k with _ | _ | _ | k
  · omega
  · omega
  · omega
  · change (a.drop 2).drop k = a.drop (k + 2)
    rw [List.drop_drop]
    congr 1
    omega

lemma alpha_lexical_first_negative_step_exists_take_one (a : List ℕ) (hlen : 1 ≤ a.length) :
    a.take 1 = [a.getD 0 0] := by
  have : 0 < a.length := by omega
  rw [List.getD_eq_getElem a 0 this]
  rcases a with _ | ⟨x, xs⟩
  · contradiction
  · rfl

theorem alpha_lexical_first_negative_step_exists (a : List ℕ)
    (ha : alpha_is_lexical a) (hlen : 2 ≤ a.length) :
    ∃ b : List ℕ, alpha_elementary_cell_step a b 1 ∧
      alpha_is_lexical b ∧ alpha_lexical_lt a b := by
  have ha1_pos : 0 < a.getD 1 0 :=
    alpha_lexical_first_negative_step_exists_cell_pos a ha 1 (by omega)
  rcases eq_or_lt_of_le (show 1 ≤ a.getD 1 0 by omega) with ha1 | ha1
  · refine ⟨[a.getD 0 0 + 1] ++ a.drop 2, ?_, ?_, ?_⟩
    · refine ⟨by omega, Or.inr ⟨by omega, ha1.symm, ?_⟩⟩
      rfl
    · have hblen : ([a.getD 0 0 + 1] ++ a.drop 2).length = a.length - 1 := by
        simp; omega
      refine ⟨by simp, fun v hv => ?_, fun k hk hk0 => ?_⟩
      · simp only [List.mem_append, List.mem_singleton] at hv
        rcases hv with rfl | hv
        · omega
        · exact ha.2.1 v (List.mem_of_mem_drop hv)
      · apply alpha_lexical_first_negative_step_exists_lt_of_first_cell_lt
        · rw [alpha_lexical_first_negative_step_exists_getD_drop_zero,
              alpha_lexical_first_negative_step_exists_getD_cons_append _ _ k hk0,
              alpha_lexical_first_negative_step_exists_getD_drop]
          have hcell := alpha_lexical_first_negative_step_exists_cell_le_first a ha (2 + (k - 1)) (by omega)
          have : ([a.getD 0 0 + 1] ++ a.drop 2).getD 0 0 = a.getD 0 0 + 1 := rfl
          omega
        · rw [hblen]; omega
    · apply alpha_lexical_first_negative_step_exists_lt_of_first_cell_lt
      · change a.getD 0 0 < a.getD 0 0 + 1; omega
      · omega
  · refine ⟨[a.getD 0 0, a.getD 1 0 - 1, 1] ++ a.drop 2, ?_, ?_, ?_⟩
    · refine ⟨by omega, Or.inl ⟨ha1, ?_⟩⟩
      rw [alpha_lexical_first_negative_step_exists_take_one a (by omega)]
      rfl
    · have hblen : ([a.getD 0 0, a.getD 1 0 - 1, 1] ++ a.drop 2).length = a.length + 1 := by
        simp only [List.length_append, List.length_cons, List.length_nil, List.length_drop]
        omega
      have hab_lt : alpha_lexical_lt a ([a.getD 0 0, a.getD 1 0 - 1, 1] ++ a.drop 2) := by
        apply alpha_lexical_first_negative_step_exists_lt_of_second_cell_gt
        · rfl
        · have : ([a.getD 0 0, a.getD 1 0 - 1, 1] ++ a.drop 2).getD 1 0 = a.getD 1 0 - 1 := rfl
          omega
        · rw [hblen]; omega
      refine ⟨by simp, fun v hv => ?_, fun k hk hk0 => ?_⟩
      · simp only [List.mem_append, List.mem_cons, List.not_mem_nil] at hv
        rcases hv with (rfl | rfl | rfl | hF) | hv
        · exact alpha_lexical_first_negative_step_exists_cell_pos a ha 0 (by omega)
        · omega
        · omega
        · contradiction
        · exact ha.2.1 v (List.mem_of_mem_drop hv)
      · rcases eq_or_ne k 1 with rfl | hk1
        · apply alpha_lexical_first_negative_step_exists_lt_of_first_cell_lt
          · rw [alpha_lexical_first_negative_step_exists_getD_drop_zero]
            have h1 : ([a.getD 0 0, a.getD 1 0 - 1, 1] ++ a.drop 2).getD 1 0 = a.getD 1 0 - 1 := rfl
            have h0 : ([a.getD 0 0, a.getD 1 0 - 1, 1] ++ a.drop 2).getD 0 0 = a.getD 0 0 := rfl
            have hle := alpha_lexical_first_negative_step_exists_cell_le_first a ha 1 (by omega)
            omega
          · rw [hblen]; omega
        · rcases eq_or_ne k 2 with rfl | hk2
          · apply alpha_lexical_first_negative_step_exists_lt_of_first_cell_lt
            · rw [alpha_lexical_first_negative_step_exists_getD_drop_zero]
              have h2 : ([a.getD 0 0, a.getD 1 0 - 1, 1] ++ a.drop 2).getD 2 0 = 1 := rfl
              have h0 : ([a.getD 0 0, a.getD 1 0 - 1, 1] ++ a.drop 2).getD 0 0 = a.getD 0 0 := rfl
              have htwo := alpha_lexical_first_negative_step_exists_two_le_first a ha hlen
              omega
            · rw [hblen]; omega
          · have hk3 : 3 ≤ k := by omega
            have hdrop_eq : ([a.getD 0 0, a.getD 1 0 - 1, 1] ++ a.drop 2).drop k = a.drop (k - 1) :=
              alpha_lexical_first_negative_step_exists_drop_ge_three a (a.getD 1 0) k hk3
            rw [hdrop_eq]
            have hkm : k - 1 < a.length := by rw [hblen] at hk; omega
            have hkm0 : 0 < k - 1 := by omega
            have hdrop_lt_a := ha.2.2 (k - 1) hkm hkm0
            exact alpha_lexical_first_negative_step_exists_lt_trans
              (a.drop (k - 1)) a ([a.getD 0 0, a.getD 1 0 - 1, 1] ++ a.drop 2) hdrop_lt_a hab_lt
    · apply alpha_lexical_first_negative_step_exists_lt_of_second_cell_gt
      · rfl
      · have : ([a.getD 0 0, a.getD 1 0 - 1, 1] ++ a.drop 2).getD 1 0 = a.getD 1 0 - 1 := rfl
        omega
      · have hblen : ([a.getD 0 0, a.getD 1 0 - 1, 1] ++ a.drop 2).length = a.length + 1 := by
          simp only [List.length_append, List.length_cons, List.length_nil, List.length_drop]
          omega
        rw [hblen]; omega
