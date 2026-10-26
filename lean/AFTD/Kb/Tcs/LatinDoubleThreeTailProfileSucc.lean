import AFTD.Prelude
import AFTD.Kb.Tcs.LatinTableaux
import AFTD.Kb.Tcs.LatinDoubleThreeTailShape
import AFTD.Kb.Tcs.LatinDoubleThreeTailProfile
import AFTD.Kb.Tcs.LatinColumnSymbols
import AFTD.Kb.Tcs.MemLatinColumnSymbols
import AFTD.Kb.Tcs.MemLatinDoubleThreeTailShape
import AFTD.Kb.Tcs.LatinDoubleThreeTailShapeRowLen
import AFTD.Kb.Tcs.LatinDoubleThreeTailShapeRowLenSucc

/-!
# latin_double_three_tail_profile_succ

Topic: combinatorics   Node: 6ba356159b24

Provenance: helper lemma. Helper for latin_double_three_tail_profile_all (the open enumeration problem of https://arxiv.org/html/2610.29291v1, Conjecture 6.3): the induction step of its plan.

Induction step for the double-3-tail staircase profile: for k >= 5, if every Latin tableau of shape (k,k-1,...,4,3,3) has the canonical column-symbol profile, then so does every Latin tableau of shape (k+1,k,...,4,3,3).
-/

theorem latin_double_three_tail_profile_succ_core (k s c : ℕ) (hk : 5 ≤ k) (hc : c < 3) (x : ℕ → ℕ)
    (hx : ∀ j ≤ k, 1 ≤ x j ∧ x j ≤ k + 1)
    (hinj : ∀ i ≤ k, ∀ j ≤ k, x i = x j → i = j)
    (h0c : x c = k - 1 ∨ x c = k + 1)
    (h0r : ∀ j < 3, j ≠ c → k ≤ x j)
    (hmid : ∀ j, 3 ≤ j → j < k - 2 → k - j < x j)
    (hpair : x (k - 2) ≤ 3 → x (k - 2) = s) :
    ∃ c', c' < 3 ∧ c' ≠ c ∧ x c' = k + 1 ∧ x c = k - 1 ∧
      (∀ j < 3, j ≠ c → j ≠ c' → x j = k) ∧
      (∀ j, 3 ≤ j → j < k - 2 → x j = k + 1 - j) ∧ x (k - 2) = s ∧
      1 ≤ x (k - 1) ∧ x (k - 1) ≤ 3 ∧ 1 ≤ x k ∧ x k ≤ 3 ∧ x k ≠ s ∧ x (k - 1) ≠ x k := by
  -- the two regular columns take k and k+1
  have hreg : ∃ c', c' < 3 ∧ c' ≠ c ∧ x c' = k + 1 ∧ ∀ j < 3, j ≠ c → j ≠ c' → x j = k := by
    have hb : ∀ j < 3, j ≠ c → x j = k ∨ x j = k + 1 := by
      intro j hj hjc
      have := h0r j hj hjc
      have := (hx j (by omega)).2
      omega
    interval_cases c
    · rcases hb 1 (by omega) (by omega) with h1 | h1
      · refine ⟨2, by omega, by omega, ?_, ?_⟩
        · rcases hb 2 (by omega) (by omega) with h2 | h2
          · exact absurd (hinj 1 (by omega) 2 (by omega) (h1.trans h2.symm)) (by omega)
          · exact h2
        · intro j hj h0 h2; have : j = 1 := by omega
          subst this; exact h1
      · refine ⟨1, by omega, by omega, h1, ?_⟩
        intro j hj h0 h1'; have : j = 2 := by omega
        subst this
        rcases hb 2 (by omega) (by omega) with h2 | h2
        · exact h2
        · exact absurd (hinj 1 (by omega) 2 (by omega) (h1.trans h2.symm)) (by omega)
    · rcases hb 0 (by omega) (by omega) with h1 | h1
      · refine ⟨2, by omega, by omega, ?_, ?_⟩
        · rcases hb 2 (by omega) (by omega) with h2 | h2
          · exact absurd (hinj 0 (by omega) 2 (by omega) (h1.trans h2.symm)) (by omega)
          · exact h2
        · intro j hj h0 h2; have : j = 0 := by omega
          subst this; exact h1
      · refine ⟨0, by omega, by omega, h1, ?_⟩
        intro j hj h0 h1'; have : j = 2 := by omega
        subst this
        rcases hb 2 (by omega) (by omega) with h2 | h2
        · exact h2
        · exact absurd (hinj 0 (by omega) 2 (by omega) (h1.trans h2.symm)) (by omega)
    · rcases hb 0 (by omega) (by omega) with h1 | h1
      · refine ⟨1, by omega, by omega, ?_, ?_⟩
        · rcases hb 1 (by omega) (by omega) with h2 | h2
          · exact absurd (hinj 0 (by omega) 1 (by omega) (h1.trans h2.symm)) (by omega)
          · exact h2
        · intro j hj h0 h2; have : j = 0 := by omega
          subst this; exact h1
      · refine ⟨0, by omega, by omega, h1, ?_⟩
        intro j hj h0 h1'; have : j = 1 := by omega
        subst this
        rcases hb 1 (by omega) (by omega) with h2 | h2
        · exact h2
        · exact absurd (hinj 0 (by omega) 1 (by omega) (h1.trans h2.symm)) (by omega)
  obtain ⟨c', hc'3, hc'c, hc'v, hrest⟩ := hreg
  have hcv : x c = k - 1 := by
    rcases h0c with h | h
    · exact h
    · exact absurd (hinj c (by omega) c' (by omega) (h.trans hc'v.symm)) (Ne.symm hc'c)
  -- values ≥ k-1 are taken by the first three columns
  have htop : ∀ j, 3 ≤ j → j ≤ k → k - 1 ≤ x j → False := by
    intro j hj3 hjk hv
    have hle := (hx j hjk).2
    have : x j = x c ∨ x j = x c' ∨ ∃ i < 3, i ≠ c ∧ i ≠ c' ∧ x j = x i := by
      by_cases h1 : x j = k - 1
      · left; omega
      by_cases h2 : x j = k + 1
      · right; left; omega
      right; right
      have hxk : x j = k := by omega
      have : ∃ i < 3, i ≠ c ∧ i ≠ c' := ⟨3 - c - c', by omega, by omega, by omega⟩
      obtain ⟨i, hi, hic, hic'⟩ := this
      exact ⟨i, hi, hic, hic', by rw [hxk, hrest i hi hic hic']⟩
    rcases this with h | h | ⟨i, hi, -, -, h⟩
    · have := hinj j hjk c (by omega) h; omega
    · have := hinj j hjk c' (by omega) h; omega
    · have := hinj j hjk i (by omega) h; omega
  -- upper bound by strong induction
  have hub : ∀ j, 3 ≤ j → j ≤ k → x j ≤ max 3 (k + 1 - j) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj3 hjk
      by_contra hcon
      push_neg at hcon
      have hv := (hx j hjk).2
      by_cases hbig : k - 1 ≤ x j
      · exact htop j hj3 hjk hbig
      · set i := k + 1 - x j with hi
        have hi3 : 3 ≤ i := by omega
        have hij : i < j := by
          rcases le_total 3 (k + 1 - j) with h | h
          · rw [max_eq_right h] at hcon; omega
          · rw [max_eq_left h] at hcon; omega
        have h1 := ih i hij hi3 (by omega)
        have hik2 : i < k - 2 := by omega
        have h2 := hmid i hi3 hik2
        have : x i = x j := by
          rw [max_eq_right (by omega)] at h1; omega
        have := hinj i (by omega) j hjk this
        omega
  have hmid' : ∀ j, 3 ≤ j → j < k - 2 → x j = k + 1 - j := by
    intro j hj3 hjk
    have h1 := hub j hj3 (by omega)
    have h2 := hmid j hj3 hjk
    rw [max_eq_right (by omega)] at h1
    omega
  have hk2 : x (k - 2) = s := by
    have h1 := hub (k - 2) (by omega) (by omega)
    rw [max_eq_left (by omega)] at h1
    exact hpair h1
  have hk1 := hub (k - 1) (by omega) (by omega)
  have hk0 := hub k (by omega) le_rfl
  rw [max_eq_left (by omega)] at hk1 hk0
  refine ⟨c', hc'3, hc'c, hc'v, hcv, hrest, hmid', hk2, (hx _ (by omega)).1, hk1,
    (hx _ le_rfl).1, hk0, ?_, ?_⟩
  · intro h
    have := hinj k le_rfl (k - 2) (by omega) (h.trans hk2.symm); omega
  · intro h
    have := hinj (k - 1) (by omega) k le_rfl h; omega

theorem latin_double_three_tail_profile_succ_lift_mem (k : ℕ) (c : (latin_double_three_tail_shape k).cells) :
    (c.1.1 + 1, c.1.2) ∈ (latin_double_three_tail_shape (k + 1)).cells := by
  have h := (mem_latin_double_three_tail_shape k c.1.1 c.1.2).mp c.2
  apply (mem_latin_double_three_tail_shape (k + 1) (c.1.1 + 1) c.1.2).mpr
  have : k + 1 - (c.1.1 + 1) = k - c.1.1 := by omega
  rw [this]
  exact ⟨by omega, h.2⟩

theorem latin_double_three_tail_profile_succ_top_mem (k j : ℕ) (hk : 1 ≤ k) (hj : j < k + 1) :
    (0, j) ∈ (latin_double_three_tail_shape (k + 1)).cells := by
  apply (mem_latin_double_three_tail_shape (k + 1) 0 j).mpr
  exact ⟨by omega, lt_of_lt_of_le (by omega) (le_max_right _ _)⟩

def latin_double_three_tail_profile_succ_restrict (k : ℕ) (T : (latin_double_three_tail_shape (k + 1)).cells → ℕ) :
    (latin_double_three_tail_shape k).cells → ℕ :=
  fun c => T ⟨(c.1.1 + 1, c.1.2), latin_double_three_tail_profile_succ_lift_mem k c⟩

theorem latin_double_three_tail_profile_succ_restrict_mem (k : ℕ) (T : (latin_double_three_tail_shape (k + 1)).cells → ℕ)
    (hT : T ∈ latin_tableaux (latin_double_three_tail_shape (k + 1))) :
    latin_double_three_tail_profile_succ_restrict k T ∈ latin_tableaux (latin_double_three_tail_shape k) := by
  simp only [latin_tableaux, Finset.mem_filter, Fintype.mem_piFinset] at hT ⊢
  obtain ⟨hb, hr, hc⟩ := hT
  refine ⟨fun c => ?_, fun c1 c2 h1 h2 => ?_, fun c1 c2 h1 h2 => ?_⟩
  · have := hb ⟨(c.1.1 + 1, c.1.2), latin_double_three_tail_profile_succ_lift_mem k c⟩
    rw [latin_double_three_tail_shape_rowLen_succ] at this
    exact this
  · exact hr ⟨_, latin_double_three_tail_profile_succ_lift_mem k c1⟩ ⟨_, latin_double_three_tail_profile_succ_lift_mem k c2⟩ (by simp [h1]) h2
  · have := hc ⟨_, latin_double_three_tail_profile_succ_lift_mem k c1⟩ ⟨_, latin_double_three_tail_profile_succ_lift_mem k c2⟩ h1 h2
    simpa using this

theorem latin_double_three_tail_profile_succ_col_succ (k j : ℕ) (hk : 1 ≤ k) (hj : j < k + 1)
    (T : (latin_double_three_tail_shape (k + 1)).cells → ℕ) :
    latin_column_symbols (latin_double_three_tail_shape (k + 1)) T j =
      insert (T ⟨(0, j), latin_double_three_tail_profile_succ_top_mem k j hk hj⟩)
        (latin_column_symbols (latin_double_three_tail_shape k) (latin_double_three_tail_profile_succ_restrict k T) j) := by
  ext x
  rw [Finset.mem_insert, mem_latin_column_symbols, mem_latin_column_symbols]
  constructor
  · rintro ⟨⟨⟨i, j'⟩, hc⟩, hj', hx⟩
    simp only at hj'
    subst hj'
    cases i with
    | zero => left; exact hx.symm
    | succ i =>
      right
      have hm : (i, j') ∈ (latin_double_three_tail_shape k).cells := by
        have h := (mem_latin_double_three_tail_shape (k + 1) (i + 1) j').mp hc
        apply (mem_latin_double_three_tail_shape k i j').mpr
        have : k + 1 - (i + 1) = k - i := by omega
        rw [this] at h
        exact ⟨by omega, h.2⟩
      exact ⟨⟨(i, j'), hm⟩, rfl, hx⟩
  · rintro (hx | ⟨c, hcj, hx⟩)
    · exact ⟨⟨(0, j), latin_double_three_tail_profile_succ_top_mem k j hk hj⟩, rfl, hx.symm⟩
    · exact ⟨⟨(c.1.1 + 1, c.1.2), latin_double_three_tail_profile_succ_lift_mem k c⟩, hcj, hx⟩

theorem latin_double_three_tail_profile_succ_col_empty (k : ℕ) (hk : 3 ≤ k) (T : (latin_double_three_tail_shape k).cells → ℕ) :
    latin_column_symbols (latin_double_three_tail_shape k) T k = ∅ := by
  ext x
  simp only [mem_latin_column_symbols, Finset.notMem_empty, iff_false]
  rintro ⟨⟨⟨i, j⟩, hc⟩, hj, -⟩
  simp only at hj
  subst hj
  have h := (mem_latin_double_three_tail_shape j i j).mp hc
  have : max 3 (j - i) ≤ j := max_le (by omega) (by omega)
  omega

theorem latin_double_three_tail_profile_succ_step (k : ℕ) (hk : 5 ≤ k)
    (T : (latin_double_three_tail_shape (k + 1)).cells → ℕ)
    (hT : T ∈ latin_tableaux (latin_double_three_tail_shape (k + 1)))
    (hprof : latin_double_three_tail_profile k (latin_double_three_tail_profile_succ_restrict k T)) :
    latin_double_three_tail_profile (k + 1) T := by
  have hT' := hT
  simp only [latin_tableaux, Finset.mem_filter, Fintype.mem_piFinset] at hT'
  obtain ⟨hb, hr, hcl⟩ := hT'
  have hk1 : 1 ≤ k := by omega
  let x : ℕ → ℕ := fun j => if h : j < k + 1 then T ⟨(0, j), latin_double_three_tail_profile_succ_top_mem k j hk1 h⟩ else 0
  have hxdef : ∀ j (h : j < k + 1), T ⟨(0, j), latin_double_three_tail_profile_succ_top_mem k j hk1 h⟩ = x j := by
    intro j h; simp only [x, dif_pos h]
  have hrow0 : (latin_double_three_tail_shape (k + 1)).rowLen 0 = k + 1 := by
    rw [latin_double_three_tail_shape_rowLen, if_pos (by omega)]
    exact max_eq_right (by omega)
  have hx : ∀ j ≤ k, 1 ≤ x j ∧ x j ≤ k + 1 := by
    intro j hj
    have := hb ⟨(0, j), latin_double_three_tail_profile_succ_top_mem k j hk1 (by omega)⟩
    rw [hxdef j (by omega)] at this
    simp only [hrow0, Finset.mem_Icc] at this
    exact this
  have hinj : ∀ i ≤ k, ∀ j ≤ k, x i = x j → i = j := by
    intro i hi j hj h
    rw [← hxdef i (by omega), ← hxdef j (by omega)] at h
    exact hr ⟨(0, i), latin_double_three_tail_profile_succ_top_mem k i hk1 (by omega)⟩
      ⟨(0, j), latin_double_three_tail_profile_succ_top_mem k j hk1 (by omega)⟩ rfl h
  have hcol : ∀ j ≤ k, x j ∉ latin_column_symbols (latin_double_three_tail_shape k)
      (latin_double_three_tail_profile_succ_restrict k T) j := by
    intro j hj hmem
    rw [mem_latin_column_symbols] at hmem
    obtain ⟨c, hcj, hcx⟩ := hmem
    rw [← hxdef j (by omega)] at hcx
    have := hcl ⟨_, latin_double_three_tail_profile_succ_lift_mem k c⟩ ⟨(0, j), latin_double_three_tail_profile_succ_top_mem k j hk1 (by omega)⟩ hcj hcx
    simp at this
  obtain ⟨s, hs, c, hc3, hfirst, hmid, hpair, hlast⟩ := hprof
  rw [Finset.mem_Icc] at hs
  have h0c : x c = k - 1 ∨ x c = k + 1 := by
    have h1 := hcol c (by omega)
    rw [hfirst c hc3, if_pos rfl] at h1
    have h2 := hx c (by omega)
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_singleton, not_or, not_and] at h1
    omega
  have h0r : ∀ j < 3, j ≠ c → k ≤ x j := by
    intro j hj hjc
    have h1 := hcol j (by omega)
    rw [hfirst j hj, if_neg hjc] at h1
    have h2 := hx j (by omega)
    simp only [Finset.mem_Icc, not_and] at h1
    omega
  have hmid0 : ∀ j, 3 ≤ j → j < k - 2 → k - j < x j := by
    intro j hj3 hjk
    have h1 := hcol j (by omega)
    rw [hmid j hj3 hjk] at h1
    have h2 := hx j (by omega)
    simp only [Finset.mem_Icc, not_and] at h1
    omega
  have hpair0 : x (k - 2) ≤ 3 → x (k - 2) = s := by
    intro h3
    have h1 := hcol (k - 2) (by omega)
    rw [hpair] at h1
    have h2 := hx (k - 2) (by omega)
    simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_singleton, not_and, not_not] at h1
    exact h1 ⟨h2.1, h3⟩
  obtain ⟨c', hc'3, hc'c, hc'v, hcv, hrest, hmid', hk2, h1a, h1b, h0a, h0b, hks, hk10⟩ :=
    latin_double_three_tail_profile_succ_core k s c hk hc3 x hx hinj h0c h0r hmid0 hpair0
  have hk1s : x (k - 1) ≠ s := by
    intro h
    have := hinj (k - 1) (by omega) (k - 2) (by omega) (h.trans hk2.symm)
    omega
  unfold latin_double_three_tail_profile
  refine ⟨x k, Finset.mem_Icc.mpr ⟨h0a, h0b⟩, c', hc'3, ?_, ?_, ?_, ?_⟩
  · intro j hj
    rw [latin_double_three_tail_profile_succ_col_succ k j hk1 (by omega), hxdef j (by omega), hfirst j hj]
    by_cases hjc : j = c
    · subst hjc
      rw [if_pos rfl, if_neg (Ne.symm hc'c), hcv]
      ext v; simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_Icc, Finset.mem_singleton]
      omega
    · rw [if_neg hjc]
      by_cases hjc' : j = c'
      · subst hjc'
        rw [if_pos rfl, hc'v]
        ext v; simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_Icc, Finset.mem_singleton]
        omega
      · rw [if_neg hjc', hrest j hj hjc hjc']
        ext v; simp only [Finset.mem_insert, Finset.mem_Icc]
        omega
  · intro j hj3 hjk
    rw [latin_double_three_tail_profile_succ_col_succ k j hk1 (by omega), hxdef j (by omega)]
    by_cases hjk2 : j < k - 2
    · rw [hmid j hj3 hjk2, hmid' j hj3 hjk2]
      ext v; simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    · have hj : j = k - 2 := by omega
      subst hj
      rw [hpair, hk2]
      ext v; simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_singleton]
      by_cases hv : v = s <;> omega
  · have e : k + 1 - 2 = k - 1 := by omega
    rw [e, latin_double_three_tail_profile_succ_col_succ k (k - 1) hk1 (by omega), hxdef (k - 1) (by omega), hlast]
    ext v; simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_singleton]
    by_cases hv : v = x k <;> omega
  · have e : k + 1 - 1 = k := by omega
    rw [e, latin_double_three_tail_profile_succ_col_succ k k hk1 (by omega), hxdef k (by omega),
      latin_double_three_tail_profile_succ_col_empty k (by omega)]
    rfl

theorem latin_double_three_tail_profile_succ (k : ℕ) (hk : 5 ≤ k)
    (ih : ∀ T ∈ latin_tableaux (latin_double_three_tail_shape k), latin_double_three_tail_profile k T) :
    ∀ T ∈ latin_tableaux (latin_double_three_tail_shape (k + 1)), latin_double_three_tail_profile (k + 1) T := by
  intro T hT
  exact latin_double_three_tail_profile_succ_step k hk T hT
    (ih _ (latin_double_three_tail_profile_succ_restrict_mem k T hT))
