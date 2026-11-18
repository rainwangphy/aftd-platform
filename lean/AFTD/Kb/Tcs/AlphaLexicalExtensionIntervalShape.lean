import AFTD.Prelude
import AFTD.Kb.Tcs.AlphaLexicalLt
import AFTD.Kb.Tcs.AlphaSignedCell
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.AlphaLexicalLtAppendParity

/-!
# alpha_lexical_extension_interval_shape

Topic: combinatorics   Node: 55a9f55ebafb

Provenance: helper lemma. Prefix-shape consequence of Lemma 2.8 of DOI:10.1006/jcta.2000.3112, used in the immediate-blocker route to OP-392, arXiv:2610.24758.

For positive sequences, anything strictly between an even extension of a nonempty base with a tail and the corresponding odd extension with a tail is the base or begins with one of those two extensions.
-/

theorem alpha_isx_signed_zero (A : List ℕ) (j : ℕ) (h : A.length ≤ j) :
    alpha_signed_cell A j = 0 := by
  unfold alpha_signed_cell
  rw [List.getD_eq_default _ _ h]; split_ifs <;> simp

theorem alpha_isx_signed_le (A B : List ℕ) (L : ℕ) (hlt : alpha_lexical_lt A B)
    (heq : ∀ j < L, alpha_signed_cell A j = alpha_signed_cell B j) :
    alpha_signed_cell A L ≤ alpha_signed_cell B L := by
  obtain ⟨r, _, hpre, hr⟩ := hlt
  rcases lt_trichotomy r L with h | h | h
  · exact absurd (heq r h) (ne_of_lt hr)
  · exact h ▸ hr.le
  · exact (hpre L h).le

theorem alpha_isx_lt_iff_first_diff (A B : List ℕ) (p : ℕ)
    (heq : ∀ j < p, alpha_signed_cell A j = alpha_signed_cell B j)
    (hne : alpha_signed_cell A p ≠ alpha_signed_cell B p) :
    alpha_lexical_lt A B ↔ alpha_signed_cell A p < alpha_signed_cell B p := by
  constructor
  · intro h
    have := alpha_isx_signed_le A B p h heq
    exact lt_of_le_of_ne this hne
  · intro hlt
    refine ⟨p, ?_, heq, hlt⟩
    by_contra hp
    push Not at hp
    apply hne
    rw [alpha_isx_signed_zero A p (le_trans (le_max_left _ _) hp),
      alpha_isx_signed_zero B p (le_trans (le_max_right _ _) hp)]

theorem alpha_isx_signed_eq_iff (A B : List ℕ) (j : ℕ) :
    alpha_signed_cell A j = alpha_signed_cell B j ↔ A.getD j 0 = B.getD j 0 := by
  unfold alpha_signed_cell
  split_ifs <;> omega

theorem alpha_isx_signed_append_left (u X : List ℕ) (j : ℕ) (hj : j < u.length) :
    alpha_signed_cell (u ++ X) j = alpha_signed_cell u j := by
  unfold alpha_signed_cell
  rw [List.getD_append _ _ _ _ hj]

theorem alpha_isx_eq_append_of_agree (w z : List ℕ) (hw : ∀ v ∈ w, 0 < v)
    (h : ∀ j < w.length, z.getD j 0 = w.getD j 0) : z = w ++ z.drop w.length := by
  have hlen : ∀ j < w.length, j < z.length := by
    intro j hj
    by_contra hc
    push Not at hc
    have hg := h j hj
    rw [List.getD_eq_default _ _ hc, List.getD_eq_getElem _ _ hj] at hg
    have := hw _ (List.getElem_mem hj)
    omega
  have htake : z.take w.length = w := by
    apply List.ext_getElem
    · simp only [List.length_take]
      rcases Nat.eq_zero_or_pos w.length with h0 | h0
      · omega
      · have := hlen (w.length - 1) (by omega); omega
    · intro j h1 h2
      have hg := h j h2
      rw [List.getD_eq_getElem _ _ (hlen j h2), List.getD_eq_getElem _ _ h2] at hg
      rw [List.getElem_take]; exact hg
  conv_lhs => rw [← List.take_append_drop w.length z]
  rw [htake]

theorem alpha_isx_cell_last (g X : List ℕ) (c : ℕ) :
    (g ++ c :: X).getD g.length 0 = c := by
  rw [List.getD_append_right _ _ _ _ le_rfl]; simp

theorem alpha_lexical_extension_interval_shape (f x y z : List ℕ) (hf : f ≠ []) (hfpos : ∀ v ∈ f, 0 < v) (hx : ∀ v ∈ x, 0 < v) (hy : ∀ v ∈ y, 0 < v) (hz : ∀ v ∈ z, 0 < v) : let e := if f.length % 2 = 0 then f.dropLast ++ [f.getLastD 0 + 1] else f ++ [1]; let o := if f.length % 2 = 0 then f ++ [1] else f.dropLast ++ [f.getLastD 0 + 1]; alpha_lexical_lt (e ++ x) z → alpha_lexical_lt z (o ++ y) → z = f ∨ (∃ t : List ℕ, z = e ++ t) ∨ (∃ t : List ℕ, z = o ++ t) := by
  intro e o hlo hhi
  obtain ⟨g, l, rfl⟩ : ∃ g l, f = g ++ [l] :=
    ⟨f.dropLast, f.getLast hf, (List.dropLast_append_getLast hf).symm⟩
  have hdl : (g ++ [l]).dropLast = g := by simp
  have hgl : (g ++ [l]).getLastD 0 = l := by simp [List.getLastD_eq_getLast?]
  have hl : 0 < l := hfpos l (by simp)
  have hg : ∀ v ∈ g, 0 < v := fun v hv => hfpos v (by simp [hv])
  have hflen : (g ++ [l]).length = g.length + 1 := by simp
  -- the two comparison lists have the form g ++ c :: X
  have heX : ∃ c X, e ++ x = g ++ c :: X ∧
      (if (g.length + 1) % 2 = 0 then c = l + 1 ∧ X = x else c = l ∧ X = 1 :: x) := by
    simp only [e, hflen, hdl, hgl]
    split_ifs with h
    · exact ⟨l + 1, x, by simp, rfl, rfl⟩
    · exact ⟨l, 1 :: x, by simp, rfl, rfl⟩
  have hoY : ∃ c Y, o ++ y = g ++ c :: Y ∧
      (if (g.length + 1) % 2 = 0 then c = l ∧ Y = 1 :: y else c = l + 1 ∧ Y = y) := by
    simp only [o, hflen, hdl, hgl]
    split_ifs with h
    · exact ⟨l, 1 :: y, by simp, rfl, rfl⟩
    · exact ⟨l + 1, y, by simp, rfl, rfl⟩
  obtain ⟨c1, X, hEX, hc1⟩ := heX
  obtain ⟨c2, Y, hOY, hc2⟩ := hoY
  rw [hEX] at hlo
  rw [hOY] at hhi
  have hgc : ∀ (c : ℕ) (W : List ℕ) j, j < g.length →
      alpha_signed_cell (g ++ c :: W) j = alpha_signed_cell g j :=
    fun c W j hj => alpha_isx_signed_append_left g _ j hj
  by_cases hall : ∀ j < g.length, alpha_signed_cell z j = alpha_signed_cell g j
  swap
  · exfalso
    push Not at hall
    classical
    let P : ℕ → Prop := fun p => p < g.length ∧ alpha_signed_cell z p ≠ alpha_signed_cell g p
    have hex : ∃ p, P p := hall
    have hp : P (Nat.find hex) := Nat.find_spec hex
    have hmin : ∀ j < Nat.find hex, alpha_signed_cell z j = alpha_signed_cell g j := by
      intro j hj
      by_contra hne
      exact Nat.find_min hex hj ⟨lt_trans hj hp.1, hne⟩
    set p := Nat.find hex
    have k1 := (alpha_isx_lt_iff_first_diff _ _ p
      (fun j hj => by rw [hgc _ _ j (by omega), hmin j hj])
      (by rw [hgc _ _ p hp.1]; exact fun h => hp.2 h.symm)).mp hlo
    have k2 := (alpha_isx_lt_iff_first_diff _ _ p
      (fun j hj => by rw [hgc _ _ j (by omega), hmin j hj])
      (by rw [hgc _ _ p hp.1]; exact hp.2)).mp hhi
    rw [hgc _ _ p hp.1] at k1 k2
    exact lt_asymm k1 k2
  · -- z agrees with g below g.length; compare at g.length
    have hlo' := alpha_isx_signed_le _ _ g.length hlo
      (fun j hj => by rw [hgc _ _ j hj, hall j hj])
    have hhi' := alpha_isx_signed_le _ _ g.length hhi
      (fun j hj => by rw [hgc _ _ j hj, hall j hj])
    have hzg : ∀ j < g.length, z.getD j 0 = g.getD j 0 :=
      fun j hj => (alpha_isx_signed_eq_iff _ _ _).mp (hall j hj)
    -- agreement with g ++ [d] when the cell at g.length is d
    have hagree : ∀ d : ℕ, 0 < d → z.getD g.length 0 = d → z = (g ++ [d]) ++ z.drop (g.length + 1) := by
      intro d hd hzd
      have := alpha_isx_eq_append_of_agree (g ++ [d]) z
        (by intro v hv; rcases List.mem_append.mp hv with hv | hv
            · exact hg v hv
            · simp at hv; omega)
        (by
          intro j hj
          simp only [List.length_append, List.length_singleton] at hj
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
          · rw [List.getD_append _ _ _ _ hj, hzg j hj]
          · subst hj; rw [hzd, List.getD_append_right _ _ _ _ le_rfl]; simp)
      simpa using this
    unfold alpha_signed_cell at hlo' hhi'
    simp only [alpha_isx_cell_last] at hlo' hhi'
    by_cases hpar : (g.length + 1) % 2 = 0
    · rw [if_pos hpar] at hc1 hc2
      obtain ⟨h1, h2⟩ := hc1
      simp only [h1, h2] at hlo hlo'
      obtain ⟨h3, h4⟩ := hc2
      simp only [h3, h4] at hhi hhi'
      have hodd : ¬ g.length % 2 = 0 := by omega
      rw [if_neg hodd, if_neg hodd] at hlo' hhi'
      rcases eq_or_ne (z.getD g.length 0) l with hzl | hzl
      · -- z starts with f
        have hzf := hagree l hl hzl
        rcases hrest : z.drop (g.length + 1) with _ | ⟨c, w⟩
        · left; rw [hzf, hrest]; simp
        · right; right
          rw [hzf, hrest] at hhi
          have hh : alpha_lexical_lt ((g ++ [l]) ++ c :: w) ((g ++ [l]) ++ 1 :: y) := by
            simpa [List.append_assoc] using hhi
          rw [alpha_lexical_lt_append_parity, if_pos (by rw [hflen]; exact hpar)] at hh
          have h2 := alpha_isx_signed_le _ _ 0 hh (by intro j hj; omega)
          have hc : 0 < c := hz c (by rw [hzf, hrest]; simp)
          simp [alpha_signed_cell] at h2
          have hc1 : c = 1 := by omega
          refine ⟨w, ?_⟩
          rw [hzf, hrest, hc1]
          simp [o, hflen, hpar]
      · right; left
        have hz1 : z.getD g.length 0 = l + 1 := by omega
        have := hagree (l + 1) (by omega) hz1
        refine ⟨z.drop (g.length + 1), ?_⟩
        rw [this]
        simp [e, hflen, hpar, hdl, hgl]
    · rw [if_neg hpar] at hc1 hc2
      obtain ⟨h1, h2⟩ := hc1
      simp only [h1, h2] at hlo hlo'
      obtain ⟨h3, h4⟩ := hc2
      simp only [h3, h4] at hhi hhi'
      have hev : g.length % 2 = 0 := by omega
      rw [if_pos hev, if_pos hev] at hlo' hhi'
      rcases eq_or_ne (z.getD g.length 0) l with hzl | hzl
      · have hzf := hagree l hl hzl
        rcases hrest : z.drop (g.length + 1) with _ | ⟨c, w⟩
        · left; rw [hzf, hrest]; simp
        · right; left
          rw [hzf, hrest] at hlo
          have hh : alpha_lexical_lt ((g ++ [l]) ++ 1 :: x) ((g ++ [l]) ++ c :: w) := by
            simpa [List.append_assoc] using hlo
          rw [alpha_lexical_lt_append_parity, if_neg (by rw [hflen]; exact hpar)] at hh
          have h2 := alpha_isx_signed_le _ _ 0 hh (by intro j hj; omega)
          have hc : 0 < c := hz c (by rw [hzf, hrest]; simp)
          simp [alpha_signed_cell] at h2
          have hc1 : c = 1 := by omega
          refine ⟨w, ?_⟩
          rw [hzf, hrest, hc1]
          simp [e, hflen, hpar]
      · right; right
        have hz1 : z.getD g.length 0 = l + 1 := by omega
        have := hagree (l + 1) (by omega) hz1
        refine ⟨z.drop (g.length + 1), ?_⟩
        rw [this]
        simp [o, hflen, hpar, hdl, hgl]
