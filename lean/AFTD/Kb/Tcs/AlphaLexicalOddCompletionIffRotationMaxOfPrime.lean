import AFTD.Prelude
import AFTD.Kb.Tcs.AlphaIsLexical
import AFTD.Kb.Tcs.AlphaBinaryPrefix
import AFTD.Kb.Tcs.AlphaLexicalLtIffInversePrefix
import AFTD.Kb.Tcs.BrgcInverse
import AFTD.Kb.Tcs.BitwordRotate
import AFTD.Kb.Tcs.BitwordIsAperiodicOfPrime
import AFTD.Kb.Tcs.BrgcInverseFlipPreservesRotationMax
import AFTD.Kb.Tcs.AlphaBinaryPrefixBounds
import AFTD.Kb.Tcs.BitwordRotateIterateCut
import AFTD.Kb.Tcs.AlphaBinaryPrefixAppend
import AFTD.Kb.Tcs.BrgcInverseLtTwoPow
import AFTD.Kb.Tcs.AlphaLexicalLt
import AFTD.Kb.Tcs.BrgcInverseAlphaBinaryPrefixCons
import AFTD.Kb.Tcs.AlphaSignedCell
import AFTD.Kb.Tcs.AlphaLexicalExampleEleven
import AFTD.Kb.Tcs.Cells
import AFTD.Kb.Tcs.Bit
import AFTD.Kb.Tcs.V

/-!
# alpha_lexical_odd_completion_iff_rotation_max_of_prime

Topic: combinatorics   Node: 85934af94382

Provenance: helper lemma. Run-length helpers for OP-392, arXiv:2610.24758, Conjecture 1; lexical sequences and elementary operations from arXiv:0810.5205, Definitions 1.1, Section 2, Theorem 3.1 and Corollary 3.3. No new research advance is claimed for these supporting statements.

The proposed encoding bridge between positive lexical sequences and nonconstant odd-parity maximum-rank necklace representatives at odd prime length.
-/

lemma alpha_rot_cl_of (L M : List ℕ) (i : ℕ) (h1 : ∀ j < i, L.getD j 0 = M.getD j 0)
    (h2 : (i % 2 = 0 ∧ L.getD i 0 < M.getD i 0) ∨ (i % 2 = 1 ∧ M.getD i 0 < L.getD i 0)) :
    alpha_lexical_lt L M := by
  have hlt : alpha_signed_cell L i < alpha_signed_cell M i := by
    unfold alpha_signed_cell
    rcases h2 with ⟨hp, h⟩ | ⟨hp, h⟩
    · rw [if_pos hp, if_pos hp]; exact_mod_cast h
    · rw [if_neg (by omega), if_neg (by omega)]; omega
  refine ⟨i, ?_, fun j hj => ?_, hlt⟩
  · by_contra hge
    push Not at hge
    rw [List.getD_eq_default _ _ (le_of_max_le_left hge),
      List.getD_eq_default _ _ (le_of_max_le_right hge)] at h2
    omega
  · unfold alpha_signed_cell; rw [h1 j hj]

lemma alpha_rot_cl_to (L M : List ℕ) (h : alpha_lexical_lt L M) :
    ∃ i, (∀ j < i, L.getD j 0 = M.getD j 0) ∧
      ((i % 2 = 0 ∧ L.getD i 0 < M.getD i 0) ∨ (i % 2 = 1 ∧ M.getD i 0 < L.getD i 0)) := by
  obtain ⟨i, -, heq, hlt⟩ := h
  refine ⟨i, fun j hj => ?_, ?_⟩
  · have := heq j hj
    unfold alpha_signed_cell at this
    split_ifs at this <;> omega
  · unfold alpha_signed_cell at hlt
    split_ifs at hlt with hp
    · left; exact ⟨hp, by exact_mod_cast hlt⟩
    · right; refine ⟨by omega, ?_⟩; omega

lemma alpha_rot_cl_asymm (L M : List ℕ) (h1 : alpha_lexical_lt L M) (h2 : alpha_lexical_lt M L) :
    False := by
  obtain ⟨i, hi1, hi2⟩ := alpha_rot_cl_to L M h1
  obtain ⟨k, hk1, hk2⟩ := alpha_rot_cl_to M L h2
  rcases lt_trichotomy i k with h | rfl | h
  · have := hk1 i h; omega
  · omega
  · have := hi1 k h; omega

lemma alpha_rot_getD_drop (a : List ℕ) (k j : ℕ) : (a.drop k).getD j 0 = a.getD (k + j) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]

lemma alpha_rot_getD_left (l l' : List ℕ) (j : ℕ) (h : j < l.length) :
    (l ++ l').getD j 0 = l.getD j 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma alpha_rot_getD_right (l l' : List ℕ) (j : ℕ) (h : l.length ≤ j) :
    (l ++ l').getD j 0 = l'.getD (j - l.length) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

lemma alpha_rot_getD_take (a : List ℕ) (k j : ℕ) (h : j < k) : (a.take k).getD j 0 = a.getD j 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos h]

/-- Cells of the rotation `drop k a ++ [1] ++ take k a`. -/
lemma alpha_rot_even_cells (a : List ℕ) (k : ℕ) (hk : k ≤ a.length) (j : ℕ) :
    (a.drop k ++ [1] ++ a.take k).getD j 0 =
      if j < a.length - k then a.getD (k + j) 0 else if j = a.length - k then 1
      else if j ≤ a.length then a.getD (j - (a.length - k + 1)) 0 else 0 := by
  have hd : (a.drop k).length = a.length - k := List.length_drop
  have ht : (a.take k).length = k := List.length_take_of_le hk
  split_ifs with h1 h2 h3
  · rw [List.append_assoc, alpha_rot_getD_left _ _ _ (by omega), alpha_rot_getD_drop]
  · rw [List.append_assoc, alpha_rot_getD_right _ _ _ (by omega), hd, h2, Nat.sub_self]; rfl
  · rw [List.append_assoc, alpha_rot_getD_right _ _ _ (by omega), hd,
      show j - (a.length - k) = (j - (a.length - k + 1)) + 1 by omega]
    simp only [List.singleton_append, List.getD_cons_succ]
    rw [alpha_rot_getD_take _ _ _ (by omega)]
  · rw [List.getD_eq_default]; simp; omega

lemma alpha_rot_even_C (a : List ℕ) (j : ℕ) :
    (a ++ [1]).getD j 0 = if j < a.length then a.getD j 0 else if j = a.length then 1 else 0 := by
  split_ifs with h1 h2
  · exact alpha_rot_getD_left _ _ _ h1
  · rw [alpha_rot_getD_right _ _ _ (by omega), h2, Nat.sub_self]; rfl
  · rw [List.getD_eq_default]; simp; omega

lemma alpha_rot_even_R_eq (a : List ℕ) (k : ℕ) (hk : k ≤ a.length) :
    (a ++ [1]).drop k ++ (a ++ [1]).take k = a.drop k ++ [1] ++ a.take k := by
  rw [List.drop_append_of_le_length hk, List.take_append_of_le_length hk]

lemma alpha_rot_cells_zero (a : List ℕ) (j : ℕ) (h : a.length ≤ j) : a.getD j 0 = 0 :=
  List.getD_eq_default _ _ h

lemma alpha_rot_cells_pos (a : List ℕ) (ha : ∀ v ∈ a, 0 < v) (j : ℕ) (h : j < a.length) :
    0 < a.getD j 0 := by
  rw [List.getD_eq_getElem _ _ h]; exact ha _ (List.getElem_mem h)

lemma alpha_rot_first_ge_two (a : List ℕ) (hlex : alpha_is_lexical a) (h2 : 2 ≤ a.length)
    (hev : a.length % 2 = 0) :
    2 ≤ a.getD 0 0 := by
  have hpos := alpha_rot_cells_pos a hlex.2.1
  -- every cell is at most the first
  have hle : ∀ k < a.length, a.getD k 0 ≤ a.getD 0 0 := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rfl
    obtain ⟨i, h1, h2⟩ := alpha_rot_cl_to _ _ (hlex.2.2 k hk hk0)
    simp only [alpha_rot_getD_drop] at h1 h2
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [add_zero] at h2; omega
    · have := h1 0 hi0; rw [add_zero] at this; omega
  by_contra hlt
  have h1 : ∀ j < a.length, a.getD j 0 = 1 := fun j hj => by
    have := hle j hj; have := hpos j hj; have := hpos 0 (by omega); omega
  obtain ⟨i, hi1, hi2⟩ := alpha_rot_cl_to _ _ (hlex.2.2 1 (by omega) (by omega))
  simp only [alpha_rot_getD_drop] at hi1 hi2
  by_cases hi : i + 1 < a.length
  · rw [h1 (1 + i) (by omega), h1 _ (by omega)] at hi2; omega
  · rw [alpha_rot_cells_zero a (1 + i) (by omega)] at hi2
    by_cases hi' : i < a.length
    · rw [h1 _ hi'] at hi2
      have : i = a.length - 1 := by omega
      omega
    · rw [alpha_rot_cells_zero a i (by omega)] at hi2; omega

theorem alpha_rot_core_even (a : List ℕ) (hne : a ≠ []) (hpos : ∀ v ∈ a, 0 < v)
    (hev : a.length % 2 = 0) :
    alpha_is_lexical a ↔ ∀ k, 0 < k → k < a.length + 1 →
      alpha_lexical_lt (a.drop k ++ [1] ++ a.take k) (a ++ [1]) := by
  set m := a.length with hm
  have hm1 : 1 ≤ m := by
    rcases a with _ | ⟨x, xs⟩
    · exact absurd rfl hne
    · simp [hm]
  have hz : ∀ j, m ≤ j → a.getD j 0 = 0 := fun j hj => alpha_rot_cells_zero a j hj
  have hp : ∀ j, j < m → 0 < a.getD j 0 := fun j hj => alpha_rot_cells_pos a hpos j hj
  have R1 : ∀ k, k ≤ m → ∀ j, j < m - k →
      (a.drop k ++ [1] ++ a.take k).getD j 0 = a.getD (k + j) 0 := by
    intro k hk j hj; rw [alpha_rot_even_cells a k hk, if_pos hj]
  have R2 : ∀ k, k ≤ m → (a.drop k ++ [1] ++ a.take k).getD (m - k) 0 = 1 := by
    intro k hk; rw [alpha_rot_even_cells a k hk, if_neg (by omega), if_pos rfl]
  have R3 : ∀ k, k ≤ m → ∀ j, j < k →
      (a.drop k ++ [1] ++ a.take k).getD (m - k + 1 + j) 0 = a.getD j 0 := by
    intro k hk j hj
    rw [alpha_rot_even_cells a k hk, if_neg (by omega), if_neg (by omega), if_pos (by omega),
      show m - k + 1 + j - (m - k + 1) = j by omega]
  have R4 : ∀ k, k ≤ m → ∀ j, m < j → (a.drop k ++ [1] ++ a.take k).getD j 0 = 0 := by
    intro k hk j hj
    rw [alpha_rot_even_cells a k hk, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have C1 : ∀ j, j < m → (a ++ [1]).getD j 0 = a.getD j 0 := by
    intro j hj; rw [alpha_rot_even_C, if_pos hj]
  have C2 : (a ++ [1]).getD m 0 = 1 := by rw [alpha_rot_even_C, if_neg (by omega), if_pos rfl]
  have C3 : ∀ j, m < j → (a ++ [1]).getD j 0 = 0 := by
    intro j hj; rw [alpha_rot_even_C, if_neg (by omega), if_neg (by omega)]
  constructor
  · intro hlex k hk0 hkm
    rcases Nat.lt_or_ge k m with hkm' | hkm'
    · obtain ⟨i, h1, h2⟩ := alpha_rot_cl_to _ _ (hlex.2.2 k hkm' hk0)
      simp only [alpha_rot_getD_drop] at h1 h2
      rcases Nat.lt_or_ge i (m - k) with hi | hi
      · apply alpha_rot_cl_of _ _ i
        · intro j hj; rw [R1 k hkm'.le j (by omega), C1 j (by omega)]; exact h1 j hj
        · rw [R1 k hkm'.le i hi, C1 i (by omega)]; exact h2
      · have hi' : i = m - k := by
          by_contra hne'
          have := h1 (m - k) (by omega)
          have := hz (k + (m - k)) (by omega)
          have := hp (m - k) (by omega)
          omega
        subst hi'
        have hzm := hz (k + (m - k)) (by omega)
        have hpm := hp (m - k) (by omega)
        have hpar : (m - k) % 2 = 0 := by omega
        by_cases hA : 1 < a.getD (m - k) 0
        · apply alpha_rot_cl_of _ _ (m - k)
          · intro j hj; rw [R1 k hkm'.le j hj, C1 j (by omega)]; exact h1 j hj
          · rw [R2 k hkm'.le, C1 _ (by omega)]; omega
        · have hA1 : a.getD (m - k) 0 = 1 := by omega
          have hk2 : 2 ≤ k := by omega
          obtain ⟨i', h1', h2'⟩ := alpha_rot_cl_to _ _
            (hlex.2.2 (m - k + 1) (by omega) (by omega))
          simp only [alpha_rot_getD_drop] at h1' h2'
          rcases Nat.lt_or_ge i' (k - 1) with hi' | hi'
          · apply alpha_rot_cl_of _ _ (m - k + 1 + i')
            · intro j hj
              rcases Nat.lt_or_ge j (m - k) with hj1 | hj1
              · rw [R1 k hkm'.le j hj1, C1 j (by omega)]; exact h1 j hj1
              · rcases Nat.eq_or_lt_of_le hj1 with hj2 | hj2
                · subst hj2; rw [R2 k hkm'.le, C1 _ (by omega)]; omega
                · obtain ⟨j', rfl⟩ : ∃ j', j = m - k + 1 + j' := ⟨j - (m - k + 1), by omega⟩
                  rw [R3 k hkm'.le j' (by omega), C1 _ (by omega)]
                  exact (h1' j' (by omega)).symm
            · rw [R3 k hkm'.le i' (by omega), C1 _ (by omega)]
              omega
          · rcases Nat.eq_or_lt_of_le hi' with hi2 | hi2
            · subst hi2
              have := hz (m - k + 1 + (k - 1)) (by omega)
              have := hp (k - 1) (by omega)
              omega
            · have := h1' (k - 1) hi2
              have := hz (m - k + 1 + (k - 1)) (by omega)
              have := hp (k - 1) (by omega)
              omega
    · have hkm2 : k = m := by omega
      subst hkm2
      have h2 : 2 ≤ a.getD 0 0 := alpha_rot_first_ge_two a hlex (by omega) hev
      apply alpha_rot_cl_of _ _ 0
      · intro j hj; omega
      · left
        refine ⟨rfl, ?_⟩
        have := R2 m le_rfl
        rw [Nat.sub_self] at this
        rw [this, C1 0 (by omega)]; omega
  · intro H
    refine ⟨hne, hpos, fun k hkm hk0 => ?_⟩
    obtain ⟨i, h1, h2⟩ := alpha_rot_cl_to _ _ (H k hk0 (by omega))
    rcases Nat.lt_or_ge i (m - k) with hi | hi
    · apply alpha_rot_cl_of _ _ i
      · intro j hj
        have := h1 j hj
        rw [R1 k hkm.le j (by omega), C1 j (by omega)] at this
        rw [alpha_rot_getD_drop]; exact this
      · rw [R1 k hkm.le i hi, C1 i (by omega)] at h2
        rw [alpha_rot_getD_drop]; exact h2
    · have hpre : ∀ j < m - k, (a.drop k).getD j 0 = a.getD j 0 := by
        intro j hj
        have := h1 j (by omega)
        rw [R1 k hkm.le j hj, C1 j (by omega)] at this
        rw [alpha_rot_getD_drop]; exact this
      have hdm : (a.drop k).getD (m - k) 0 = 0 := by
        rw [alpha_rot_getD_drop]; exact hz _ (by omega)
      have hpm := hp (m - k) (by omega)
      have hwit : (m - k) % 2 = 0 → alpha_lexical_lt (a.drop k) a := by
        intro hpar
        apply alpha_rot_cl_of _ _ (m - k) hpre
        left; omega
      rcases Nat.eq_or_lt_of_le hi with hi2 | hi2
      · subst hi2
        rw [R2 k hkm.le, C1 _ (by omega)] at h2
        apply hwit; omega
      · have h1m := h1 (m - k) hi2
        rw [R2 k hkm.le, C1 _ (by omega)] at h1m
        by_cases hpar : (m - k) % 2 = 0
        · exact hwit hpar
        · exfalso
          -- the rotation by m - k + 1 beats the completion
          have hi3 : i ≤ m := by
            by_contra hgt
            rw [R4 k hkm.le i (by omega), C3 i (by omega)] at h2
            omega
          obtain ⟨i'', rfl⟩ : ∃ i'', i = m - k + 1 + i'' := ⟨i - (m - k + 1), by omega⟩
          have hk' := H (m - k + 1) (by omega) (by omega)
          rcases Nat.lt_or_ge i'' (k - 1) with hi4 | hi4
          · apply alpha_rot_cl_asymm _ _ hk'
            apply alpha_rot_cl_of _ _ i''
            · intro j hj
              have := h1 (m - k + 1 + j) (by omega)
              rw [R3 k hkm.le j (by omega), C1 _ (by omega)] at this
              rw [C1 j (by omega), R1 (m - k + 1) (by omega) j (by omega),
                show m - k + 1 + j = m - k + 1 + j from rfl]
              exact this
            · rw [R3 k hkm.le i'' (by omega), C1 _ (by omega)] at h2
              rw [C1 i'' (by omega), R1 (m - k + 1) (by omega) i'' (by omega)]
              omega
          · have hi5 : i'' = k - 1 := by omega
            subst hi5
            rw [R3 k hkm.le (k - 1) (by omega), show m - k + 1 + (k - 1) = m by omega, C2] at h2
            have := hp (k - 1) (by omega)
            omega


lemma alpha_rot_cells (C : List ℕ) (k : ℕ) (hk : k ≤ C.length) (j : ℕ) :
    (C.drop k ++ C.take k).getD j 0 =
      if j < C.length - k then C.getD (k + j) 0 else if j < C.length then
        C.getD (j - (C.length - k)) 0 else 0 := by
  have hd : (C.drop k).length = C.length - k := List.length_drop
  have ht : (C.take k).length = k := List.length_take_of_le hk
  split_ifs with h1 h2
  · rw [alpha_rot_getD_left _ _ _ (by omega), alpha_rot_getD_drop]
  · rw [alpha_rot_getD_right _ _ _ (by omega), hd, alpha_rot_getD_take _ _ _ (by omega)]
  · rw [List.getD_eq_default]; simp; omega

theorem alpha_rot_core_odd (a' : List ℕ) (c : ℕ) (hpos : ∀ v ∈ a' ++ [c], 0 < v)
    (hodd : (a' ++ [c]).length % 2 = 1) :
    alpha_is_lexical (a' ++ [c]) ↔ ∀ k, 0 < k → k < a'.length + 1 →
      alpha_lexical_lt ((a' ++ [c + 1]).drop k ++ (a' ++ [c + 1]).take k) (a' ++ [c + 1]) := by
  set a := a' ++ [c] with ha
  set C := a' ++ [c + 1] with hC
  have hlen : a.length = a'.length + 1 := by simp [ha]
  have hCl : C.length = a'.length + 1 := by simp [hC]
  set m := a'.length + 1 with hm
  have hne : a ≠ [] := by simp [ha]
  have hz : ∀ j, m ≤ j → a.getD j 0 = 0 := fun j hj => alpha_rot_cells_zero a j (by omega)
  have hp : ∀ j, j < m → 0 < a.getD j 0 := fun j hj => alpha_rot_cells_pos a hpos j (by omega)
  have hAc : a.getD (m - 1) 0 = c := by
    rw [ha, alpha_rot_getD_right _ _ _ (by omega), show m - 1 - a'.length = 0 by omega]; rfl
  have C1 : ∀ j, j < m - 1 → C.getD j 0 = a.getD j 0 := by
    intro j hj; rw [hC, ha, alpha_rot_getD_left _ _ _ (by omega), alpha_rot_getD_left _ _ _ (by omega)]
  have C2 : C.getD (m - 1) 0 = a.getD (m - 1) 0 + 1 := by
    rw [hAc, hC, alpha_rot_getD_right _ _ _ (by omega), show m - 1 - a'.length = 0 by omega]; rfl
  have C3 : ∀ j, m ≤ j → C.getD j 0 = 0 := fun j hj => alpha_rot_cells_zero C j (by omega)
  have R1 : ∀ k, k ≤ m → ∀ j, j < m - k - 1 →
      (C.drop k ++ C.take k).getD j 0 = a.getD (k + j) 0 := by
    intro k hk j hj; rw [alpha_rot_cells C k (by omega), if_pos (by omega), C1 _ (by omega)]
  have R2 : ∀ k, 1 ≤ k → k < m → ∀ j, j = m - k - 1 →
      (C.drop k ++ C.take k).getD j 0 = a.getD (m - 1) 0 + 1 := by
    intro k hk1 hk j hj
    rw [alpha_rot_cells C k (by omega), if_pos (show j < C.length - k by omega),
      show k + j = m - 1 by omega, C2]
  have R3 : ∀ k, k < m → ∀ j, j < k →
      (C.drop k ++ C.take k).getD (m - k + j) 0 = a.getD j 0 := by
    intro k hk j hj
    rw [alpha_rot_cells C k (by omega), if_neg (by omega), if_pos (by omega),
      show m - k + j - (C.length - k) = j by omega, C1 _ (by omega)]
  have R4 : ∀ k, k ≤ m → ∀ j, m ≤ j → (C.drop k ++ C.take k).getD j 0 = 0 := by
    intro k hk j hj; rw [alpha_rot_cells C k (by omega), if_neg (by omega), if_neg (by omega)]
  have D : ∀ k j, (a.drop k).getD j 0 = a.getD (k + j) 0 := fun k j => alpha_rot_getD_drop a k j
  constructor
  · intro hlex k hk0 hkm
    obtain ⟨i, h1, h2⟩ := alpha_rot_cl_to _ _ (hlex.2.2 k (by omega) hk0)
    simp only [D] at h1 h2
    rcases Nat.lt_or_ge i (m - k - 1) with hi | hi
    · apply alpha_rot_cl_of _ _ i
      · intro j hj; rw [R1 k (by omega) j (by omega), C1 j (by omega)]; exact h1 j hj
      · rw [R1 k (by omega) i hi, C1 i (by omega)]; exact h2
    rcases Nat.eq_or_lt_of_le hi with hi2 | hi2
    · subst hi2
      rw [show k + (m - k - 1) = m - 1 by omega] at h2
      have hpre : ∀ j < m - k - 1, (C.drop k ++ C.take k).getD j 0 = C.getD j 0 := by
        intro j hj; rw [R1 k (by omega) j hj, C1 j (by omega)]; exact h1 j hj
      by_cases hpar : (m - k - 1) % 2 = 1
      · apply alpha_rot_cl_of _ _ (m - k - 1) hpre
        rw [R2 k hk0 (by omega) _ rfl, C1 _ (by omega)]; omega
      by_cases hgap : a.getD (m - 1) 0 + 1 < a.getD (m - k - 1) 0
      · apply alpha_rot_cl_of _ _ (m - k - 1) hpre
        rw [R2 k hk0 (by omega) _ rfl, C1 _ (by omega)]; omega
      have heqv : a.getD (m - k - 1) 0 = a.getD (m - 1) 0 + 1 := by omega
      obtain ⟨i', h1', h2'⟩ := alpha_rot_cl_to _ _ (hlex.2.2 (m - k) (by omega) (by omega))
      simp only [D] at h1' h2'
      have hpre2 : ∀ j < m - k, (C.drop k ++ C.take k).getD j 0 = C.getD j 0 := by
        intro j hj
        rcases Nat.lt_or_ge j (m - k - 1) with hj1 | hj1
        · exact hpre j hj1
        · rw [R2 k hk0 (by omega) j (by omega), C1 _ (by omega), show j = m - k - 1 by omega,
            heqv]
      rcases Nat.lt_or_ge i' (k - 1) with hi' | hi'
      · apply alpha_rot_cl_of _ _ (m - k + i')
        · intro j hj
          rcases Nat.lt_or_ge j (m - k) with hj1 | hj1
          · exact hpre2 j hj1
          · obtain ⟨j', rfl⟩ : ∃ j', j = m - k + j' := ⟨j - (m - k), by omega⟩
            rw [R3 k (by omega) j' (by omega), C1 _ (by omega)]
            exact (h1' j' (by omega)).symm
        · rw [R3 k (by omega) i' (by omega), C1 _ (by omega)]; omega
      · apply alpha_rot_cl_of _ _ (m - k + (k - 1))
        · intro j hj
          rcases Nat.lt_or_ge j (m - k) with hj1 | hj1
          · exact hpre2 j hj1
          · obtain ⟨j', rfl⟩ : ∃ j', j = m - k + j' := ⟨j - (m - k), by omega⟩
            rw [R3 k (by omega) j' (by omega), C1 _ (by omega)]
            exact (h1' j' (by omega)).symm
        · rw [R3 k (by omega) (k - 1) (by omega), show m - k + (k - 1) = m - 1 by omega, C2]
          rcases Nat.eq_or_lt_of_le hi' with hi3 | hi3
          · subst hi3
            rw [show m - k + (k - 1) = m - 1 by omega] at h2'
            omega
          · have := h1' (k - 1) hi3
            rw [show m - k + (k - 1) = m - 1 by omega] at this
            omega
    · have h1a := h1 (m - k - 1) hi2
      rw [show k + (m - k - 1) = m - 1 by omega] at h1a
      have hi3 : i = m - k := by
        by_contra hne'
        have := h1 (m - k) (by omega)
        have := hz (k + (m - k)) (by omega)
        have := hp (m - k) (by omega)
        omega
      subst hi3
      have := hz (k + (m - k)) (by omega)
      have := hp (m - k) (by omega)
      apply alpha_rot_cl_of _ _ (m - k - 1)
      · intro j hj; rw [R1 k (by omega) j hj, C1 j (by omega)]; exact h1 j (by omega)
      · rw [R2 k hk0 (by omega) _ rfl, C1 _ (by omega)]; omega
  · intro H
    refine ⟨hne, hpos, fun k hkm hk0 => ?_⟩
    obtain ⟨i, h1, h2⟩ := alpha_rot_cl_to _ _ (H k hk0 (by omega))
    have hpre : ∀ j, j < i → j < m - k - 1 → (a.drop k).getD j 0 = a.getD j 0 := by
      intro j hj hj'
      have := h1 j hj
      rw [R1 k (by omega) j hj', C1 j (by omega)] at this
      rw [D]; exact this
    rcases Nat.lt_or_ge i (m - k - 1) with hi | hi
    · apply alpha_rot_cl_of _ _ i (fun j hj => hpre j hj (by omega))
      rw [R1 k (by omega) i hi, C1 i (by omega)] at h2
      rw [D]; exact h2
    have hd1 : (a.drop k).getD (m - k - 1) 0 = a.getD (m - 1) 0 := by
      rw [D, show k + (m - k - 1) = m - 1 by omega]
    have hd2 : (a.drop k).getD (m - k) 0 = 0 := by rw [D]; exact hz _ (by omega)
    have hpm := hp (m - k) (by omega)
    rcases Nat.eq_or_lt_of_le hi with hi2 | hi2
    · subst hi2
      rw [R2 k hk0 (by omega) _ rfl, C1 _ (by omega)] at h2
      by_cases hpar : (m - k - 1) % 2 = 0
      · apply alpha_rot_cl_of _ _ (m - k - 1) (fun j hj => hpre j hj hj)
        rw [hd1]; omega
      by_cases hlt : a.getD (m - k - 1) 0 < a.getD (m - 1) 0
      · apply alpha_rot_cl_of _ _ (m - k - 1) (fun j hj => hpre j hj hj)
        rw [hd1]; omega
      · apply alpha_rot_cl_of _ _ (m - k)
        · intro j hj
          rcases Nat.lt_or_ge j (m - k - 1) with hj1 | hj1
          · exact hpre j hj1 hj1
          · rw [show j = m - k - 1 by omega, hd1]; omega
        · rw [hd2]; omega
    · have h1m := h1 (m - k - 1) hi2
      rw [R2 k hk0 (by omega) _ rfl, C1 _ (by omega)] at h1m
      by_cases hpar : (m - k - 1) % 2 = 0
      · apply alpha_rot_cl_of _ _ (m - k - 1) (fun j hj => hpre j (by omega) hj)
        rw [hd1]; omega
      exfalso
      have hi3 : i < m := by
        by_contra hge
        rw [R4 k (by omega) i (by omega), C3 i (by omega)] at h2
        omega
      obtain ⟨i'', rfl⟩ : ∃ i'', i = m - k + i'' := ⟨i - (m - k), by omega⟩
      have hk' := H (m - k) (by omega) (by omega)
      apply alpha_rot_cl_asymm _ _ hk'
      apply alpha_rot_cl_of _ _ i''
      · intro j hj
        have := h1 (m - k + j) (by omega)
        rw [R3 k (by omega) j (by omega), C1 _ (by omega)] at this
        rw [C1 j (by omega), R1 (m - k) (by omega) j (by omega)]
        exact this
      · rw [R3 k (by omega) i'' (by omega)] at h2
        rw [C1 i'' (by omega)]
        rcases Nat.lt_or_ge i'' (k - 1) with hi4 | hi4
        · rw [C1 _ (by omega)] at h2
          rw [R1 (m - k) (by omega) i'' (by omega)]
          omega
        · have hi5 : i'' = k - 1 := by omega
          subst hi5
          rw [show m - k + (k - 1) = m - 1 by omega, C2] at h2
          rw [R2 (m - k) (by omega) (by omega) (k - 1) (by omega)]
          omega


lemma alpha_rot_bp_top (C : List ℕ) (hC : C ≠ []) (hpos : ∀ v ∈ C, 0 < v) :
    2 ^ (C.sum - 1) ≤ brgc_inverse C.sum (alpha_binary_prefix C) := by
  match C, hC with
  | z :: zs, _ =>
    have hz : 0 < z := hpos z (by simp)
    have hzs : ∀ v ∈ zs, 0 < v := fun v hv => hpos v (by simp [hv])
    rw [brgc_inverse_alpha_binary_prefix_cons z zs hz hzs, List.sum_cons]
    have h1 : 2 ^ (z - 1) ≤ 2 ^ z - 1 := by
      have : 2 ^ z = 2 * 2 ^ (z - 1) := by
        rw [← pow_succ']; congr 1; omega
      have := Nat.one_le_two_pow (n := z - 1)
      omega
    calc 2 ^ (z + zs.sum - 1) = 2 ^ zs.sum * 2 ^ (z - 1) := by
          rw [← pow_add]; congr 1; omega
      _ ≤ 2 ^ zs.sum * (2 ^ z - 1) := Nat.mul_le_mul_left _ h1
      _ ≤ _ := Nat.le_add_right _ _

lemma alpha_rot_binv_lt_half (n y : ℕ) (hn : 1 ≤ n) (hy : y < 2 ^ (n - 1)) :
    brgc_inverse n y < 2 ^ (n - 1) := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hy ⊢
  rw [brgc_inverse]
  exact Nat.xor_lt_two_pow hy (brgc_inverse_lt_two_pow (lt_of_le_of_lt (Nat.div_le_self _ _) hy))

lemma alpha_rot_sum_split (C : List ℕ) (k : ℕ) : (C.take k).sum + (C.drop k).sum = C.sum := by
  rw [← List.sum_append, List.take_append_drop]

lemma alpha_rot_drop_sum_pos (C : List ℕ) (hpos : ∀ v ∈ C, 0 < v) (k : ℕ) (hk : k < C.length) :
    0 < (C.drop k).sum := by
  rw [List.drop_eq_getElem_cons hk, List.sum_cons]
  have := hpos _ (List.getElem_mem hk); omega

lemma alpha_rot_take_sum_pos (C : List ℕ) (hpos : ∀ v ∈ C, 0 < v) (k : ℕ) (hk0 : 0 < k)
    (hk : k ≤ C.length) : 0 < (C.take k).sum := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  match C, hk with
  | z :: zs, _ =>
    simp only [List.take_succ_cons, List.sum_cons]
    have := hpos z (by simp); omega

/-- At a run start the rotated code is the code of the cyclic cell rotation. -/
lemma alpha_rot_run_iff (n : ℕ) (C : List ℕ) (hpos : ∀ v ∈ C, 0 < v) (hsum : C.sum = n)
    (hn : 2 ≤ n) (h0 : 0 < alpha_binary_prefix C) (h1 : alpha_binary_prefix C < 2 ^ n - 1)
    (k : ℕ) :
    brgc_inverse n ((bitword_rotate n)^[(C.take k).sum] (alpha_binary_prefix C)) <
        brgc_inverse n (alpha_binary_prefix C) ↔
      alpha_lexical_lt (C.drop k ++ C.take k) C := by
  have ht : ∀ v ∈ C.take k, 0 < v := fun v hv => hpos v (List.mem_of_mem_take hv)
  have hd : ∀ v ∈ C.drop k, 0 < v := fun v hv => hpos v (List.mem_of_mem_drop hv)
  have hsplit := alpha_rot_sum_split C k
  have hC : C.take k ++ C.drop k = C := List.take_append_drop k C
  have hrot : (bitword_rotate n)^[(C.take k).sum] (alpha_binary_prefix C) =
      alpha_binary_prefix (C.drop k ++ C.take k) := by
    have hx : alpha_binary_prefix C =
        2 ^ (C.drop k).sum * alpha_binary_prefix (C.take k) + alpha_binary_prefix (C.drop k) := by
      have := alpha_binary_prefix_append (C.take k) (C.drop k)
      rwa [hC] at this
    rw [alpha_binary_prefix_append (C.drop k) (C.take k), hx]
    rw [hx] at h0 h1
    exact bitword_rotate_iterate_cut hn (by omega) (alpha_binary_prefix_bounds_lt _ ht)
      (alpha_binary_prefix_bounds_lt _ hd) h0 h1
  have hRpos : ∀ v ∈ C.drop k ++ C.take k, 0 < v := by
    intro v hv; rcases List.mem_append.mp hv with h | h
    · exact hd v h
    · exact ht v h
  have hRsum : (C.drop k ++ C.take k).sum = n := by rw [List.sum_append]; omega
  rw [hrot, alpha_lexical_lt_iff_inverse_prefix _ _ hRpos hpos (by omega), hRsum, hsum]

/-- Away from run starts the rotated code has top bit zero. -/
lemma alpha_rot_nonrun_lt (n : ℕ) (C : List ℕ) (hpos : ∀ v ∈ C, 0 < v) (hsum : C.sum = n)
    (hn : 2 ≤ n) (h0 : 0 < alpha_binary_prefix C) (h1 : alpha_binary_prefix C < 2 ^ n - 1)
    (r : ℕ) (hr0 : 0 < r) (hrn : r < n) (hnot : ∀ k, (C.take k).sum ≠ r) :
    brgc_inverse n ((bitword_rotate n)^[r] (alpha_binary_prefix C)) <
        brgc_inverse n (alpha_binary_prefix C) := by
  classical
  have hex : ∃ k, r < (C.take (k + 1)).sum := ⟨C.length, by
    rw [List.take_of_length_le (by omega)]; omega⟩
  set k := Nat.find hex with hkdef
  have hk : r < (C.take (k + 1)).sum := Nat.find_spec hex
  have hkle : (C.take k).sum < r := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h]; simp; omega
    · have := Nat.find_min hex (show k - 1 < k by omega)
      rw [show k - 1 + 1 = k by omega] at this
      have := hnot k
      omega
  have hkl : k < C.length := by
    by_contra hge
    rw [List.take_of_length_le (by omega)] at hkle
    omega
  set T := C.take k
  set c := C[k]
  set Dl := C.drop (k + 1)
  have hCeq : C = T ++ c :: Dl := by
    rw [← List.drop_eq_getElem_cons hkl, List.take_append_drop]
  have htk : C.take (k + 1) = T ++ [c] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hkl]; rfl
  rw [htk, List.sum_append] at hk
  simp only [List.sum_cons, List.sum_nil, add_zero] at hk
  have hTpos : ∀ v ∈ T, 0 < v := fun v hv => hpos v (List.mem_of_mem_take hv)
  have hDpos : ∀ v ∈ Dl, 0 < v := fun v hv => hpos v (List.mem_of_mem_drop hv)
  have hsum' : T.sum + c + Dl.sum = n := by
    rw [← hsum, hCeq]; simp [List.sum_append]; omega
  set q := r - T.sum with hq
  have hq0 : 0 < q := by omega
  have hqc : q < c := by omega
  have hbT := alpha_binary_prefix_bounds_lt T hTpos
  have hbD := alpha_binary_prefix_bounds_lt Dl hDpos
  set U := 2 ^ q * alpha_binary_prefix T + 2 ^ (q - 1) with hU
  set V := alpha_binary_prefix Dl with hV
  have hx : alpha_binary_prefix C = 2 ^ (n - r) * U + V := by
    rw [hCeq, alpha_binary_prefix_append]
    simp only [alpha_binary_prefix, List.sum_cons]
    rw [hU, Nat.mul_add, ← mul_assoc, ← pow_add, ← pow_add,
      show n - r + q = c + Dl.sum by omega, show n - r + (q - 1) = c - 1 + Dl.sum by omega]
    ring
  have hUlt : U < 2 ^ r := by
    have h2 : 2 ^ r = 2 ^ q * 2 ^ T.sum := by rw [← pow_add]; congr 1; omega
    have hq2 : 2 ^ q = 2 * 2 ^ (q - 1) := by rw [← pow_succ']; congr 1; omega
    have : 2 ^ q * alpha_binary_prefix T + 2 ^ q ≤ 2 ^ q * 2 ^ T.sum := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hbT
    have := Nat.two_pow_pos (q - 1)
    omega
  have hVlt : V < 2 ^ (n - r - 1) :=
    lt_of_lt_of_le hbD (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hVlt' : V < 2 ^ (n - r) :=
    lt_of_lt_of_le hVlt (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hrot : (bitword_rotate n)^[r] (alpha_binary_prefix C) = 2 ^ r * V + U := by
    rw [hx] at h0 h1 ⊢
    exact bitword_rotate_iterate_cut hn (by omega) hUlt hVlt' h0 h1
  have hsmall : 2 ^ r * V + U < 2 ^ (n - 1) := by
    have h2 : 2 ^ (n - 1) = 2 ^ r * 2 ^ (n - r - 1) := by rw [← pow_add]; congr 1; omega
    have : 2 ^ r * V + 2 ^ r ≤ 2 ^ r * 2 ^ (n - r - 1) := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hVlt
    omega
  have hCne : C ≠ [] := by rintro rfl; simp at hkl
  have htop := alpha_rot_bp_top C hCne hpos
  rw [hsum] at htop
  rw [hrot]
  exact lt_of_lt_of_le (alpha_rot_binv_lt_half n _ (by omega) hsmall) htop


lemma alpha_rot_first_ge_two_of_rot (C : List ℕ) (hpos : ∀ v ∈ C, 0 < v) (hl : 2 ≤ C.length)
    (H : ∀ k, 0 < k → k < C.length → alpha_lexical_lt (C.drop k ++ C.take k) C) :
    2 ≤ C.getD 0 0 := by
  have hp : ∀ j, j < C.length → 0 < C.getD j 0 := fun j hj => alpha_rot_cells_pos C hpos j hj
  by_contra hlt
  have h01 : C.getD 0 0 = 1 := by have := hp 0 (by omega); omega
  have hall : ∀ k, k < C.length → C.getD k 0 = 1 := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact h01
    obtain ⟨i, h1, h2⟩ := alpha_rot_cl_to _ _ (H k hk0 hk)
    have hR0 := alpha_rot_cells C k hk.le 0
    rw [if_pos (by omega), add_zero] at hR0
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [hR0, h01] at h2; have := hp k hk; omega
    · have := h1 0 hi0; rw [hR0, h01] at this; exact this
  obtain ⟨i, h1, h2⟩ := alpha_rot_cl_to _ _ (H 1 (by omega) (by omega))
  have hR := alpha_rot_cells C 1 (by omega) i
  by_cases hi : i < C.length
  · rw [hall i hi] at h2
    split_ifs at hR with hA hB
    · rw [hR, hall _ (by omega)] at h2; omega
    · rw [hR, hall _ (by omega)] at h2; omega
  · rw [if_neg (by omega), if_neg (by omega)] at hR
    rw [hR, alpha_rot_cells_zero C i (by omega)] at h2; omega

lemma alpha_rot_bp_lt_of_first (n : ℕ) (C : List ℕ) (hpos : ∀ v ∈ C, 0 < v) (hsum : C.sum = n)
    (hn3 : 3 ≤ n) (h2 : 2 ≤ C.getD 0 0) : alpha_binary_prefix C < 2 ^ n - 1 := by
  match C, hpos, hsum, h2 with
  | [], _, hsum, _ => simp at hsum; omega
  | z :: zs, hpos, hsum, h2 =>
    simp only [List.getD_cons_zero] at h2
    have hzs : ∀ v ∈ zs, 0 < v := fun v hv => hpos v (by simp [hv])
    simp only [List.sum_cons] at hsum
    have hb := alpha_binary_prefix_bounds_lt zs hzs
    have hP : 2 ^ zs.sum ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hP2 : 2 ≤ 2 ^ (n - 2) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have e1 : 2 ^ (z - 1 + zs.sum) = 2 * 2 ^ (n - 2) := by
      rw [← pow_succ']; congr 1; omega
    have e2 : 2 ^ n = 4 * 2 ^ (n - 2) := by
      rw [show n = n - 2 + 2 by omega, pow_add]; norm_num; ring
    simp only [alpha_binary_prefix]
    omega

lemma alpha_rot_glue (n : ℕ) (C : List ℕ) (hpos : ∀ v ∈ C, 0 < v) (hsum : C.sum = n)
    (hn3 : 3 ≤ n) :
    (∀ k, 0 < k → k < C.length → alpha_lexical_lt (C.drop k ++ C.take k) C) ↔
      (0 < alpha_binary_prefix C ∧ alpha_binary_prefix C < 2 ^ n - 1 ∧
        ∀ r : ℕ, 0 < r → r < n →
          brgc_inverse n ((bitword_rotate n)^[r] (alpha_binary_prefix C)) <
            brgc_inverse n (alpha_binary_prefix C)) := by
  have hCne : C ≠ [] := by rintro rfl; simp at hsum; omega
  have hlow : 2 ^ (n - 1) ≤ alpha_binary_prefix C := by
    have := (alpha_binary_prefix_bounds C hCne hpos).1; rwa [hsum] at this
  have h0 : 0 < alpha_binary_prefix C := lt_of_lt_of_le (Nat.two_pow_pos _) hlow
  constructor
  · intro H
    have h2 : 2 ≤ C.getD 0 0 := by
      by_cases hl : 2 ≤ C.length
      · exact alpha_rot_first_ge_two_of_rot C hpos hl H
      · match C, hCne, hl, hsum with
        | [z], _, _, hsum => simp at hsum ⊢; omega
        | z :: y :: ys, _, hl, _ => simp at hl
    have h1 := alpha_rot_bp_lt_of_first n C hpos hsum hn3 h2
    refine ⟨h0, h1, fun r hr0 hrn => ?_⟩
    by_cases hrun : ∃ k, (C.take k).sum = r
    · obtain ⟨k, rfl⟩ := hrun
      have hk0 : 0 < k := by
        rcases Nat.eq_zero_or_pos k with rfl | h
        · simp at hr0
        · exact h
      have hkl : k < C.length := by
        by_contra hge
        rw [List.take_of_length_le (by omega)] at hrn; omega
      exact (alpha_rot_run_iff n C hpos hsum (by omega) h0 h1 k).mpr (H k hk0 hkl)
    · push Not at hrun
      exact alpha_rot_nonrun_lt n C hpos hsum (by omega) h0 h1 r hr0 hrn hrun
  · rintro ⟨-, h1, H⟩ k hk0 hkl
    have hs := alpha_rot_sum_split C k
    have := alpha_rot_take_sum_pos C hpos k hk0 hkl.le
    have := alpha_rot_drop_sum_pos C hpos k hkl
    exact (alpha_rot_run_iff n C hpos hsum (by omega) h0 h1 k).mp (H _ (by omega) (by omega))

lemma alpha_rot_completion_even (a : List ℕ) :
    2 * alpha_binary_prefix a + 1 = alpha_binary_prefix (a ++ [1]) := by
  rw [alpha_binary_prefix_append]
  simp [alpha_binary_prefix]

lemma alpha_rot_completion_odd (a : List ℕ) (c : ℕ) (hc : 0 < c) :
    2 * alpha_binary_prefix (a ++ [c]) = alpha_binary_prefix (a ++ [c + 1]) := by
  rw [alpha_binary_prefix_append, alpha_binary_prefix_append]
  simp only [alpha_binary_prefix, List.sum_cons, List.sum_nil, add_zero, Nat.add_sub_cancel]
  obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  simp only [Nat.add_sub_cancel, pow_succ]
  ring

theorem alpha_lexical_odd_completion_iff_rotation_max_of_prime (n : ℕ)
    (hn : n.Prime) (hn3 : 3 ≤ n) (a : List ℕ) (hne : a ≠ [])
    (ha : ∀ v ∈ a, 0 < v) (hs : a.sum + 1 = n) :
    alpha_is_lexical a ↔
      let x := 2 * alpha_binary_prefix a + (a.length + 1) % 2
      0 < x ∧ x < 2 ^ n - 1 ∧
        ∀ r : ℕ, 0 < r → r < n →
          brgc_inverse n ((bitword_rotate n)^[r] x) < brgc_inverse n x := by
  dsimp only
  rcases Nat.mod_two_eq_zero_or_one a.length with hev | hodd
  · rw [show (a.length + 1) % 2 = 1 by omega, alpha_rot_completion_even a]
    have hCpos : ∀ v ∈ a ++ [1], 0 < v := by
      intro v hv; rcases List.mem_append.mp hv with h | h
      · exact ha v h
      · simp at h; omega
    have hCsum : (a ++ [1]).sum = n := by simp; omega
    rw [← alpha_rot_glue n _ hCpos hCsum hn3, alpha_rot_core_even a hne ha hev]
    simp only [List.length_append, List.length_singleton]
    constructor
    · intro H k hk0 hk; rw [alpha_rot_even_R_eq a k (by omega)]; exact H k hk0 hk
    · intro H k hk0 hk; rw [← alpha_rot_even_R_eq a k (by omega)]; exact H k hk0 hk
  · rcases List.eq_nil_or_concat' a with h | ⟨a', c, rfl⟩
    · exact absurd h hne
    have hc : 0 < c := ha c (by simp)
    rw [show ((a' ++ [c]).length + 1) % 2 = 0 by omega, add_zero,
      alpha_rot_completion_odd a' c hc]
    have hCpos : ∀ v ∈ a' ++ [c + 1], 0 < v := by
      intro v hv; rcases List.mem_append.mp hv with h | h
      · exact ha v (by simp [h])
      · simp at h; omega
    have hCsum : (a' ++ [c + 1]).sum = n := by simp at hs ⊢; omega
    rw [← alpha_rot_glue n _ hCpos hCsum hn3, alpha_rot_core_odd a' c ha hodd]
    simp only [List.length_append, List.length_singleton]
