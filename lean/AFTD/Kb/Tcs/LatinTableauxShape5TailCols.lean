import AFTD.Prelude
import AFTD.Kb.Tcs.LatinDoubleThreeTailShape
import AFTD.Kb.Tcs.LatinTableaux
import AFTD.Kb.Tcs.LatinColumnSymbols
import AFTD.Kb.Tcs.MemLatinDoubleThreeTailShape
import AFTD.Kb.Tcs.MemLatinColumnSymbols
import AFTD.Kb.Tcs.LatinDoubleThreeTailShapeRowLen

/-!
# latin_tableaux_shape5_tail_cols

Topic: combinatorics   Node: ca96fc5fbd27

Provenance: helper lemma. step towards latin_double_three_tail_profile_base

In every Latin tableau of shape (5,4,3,3), column 4 contains a singleton {s} with s ∈ {1,2,3}, and column 3 contains {1,2,3} \ {s}.
-/

open Finset

def latin_tableaux_shape5_tail_cols_c00 : (latin_double_three_tail_shape 5).cells := ⟨(0, 0), by decide⟩
def latin_tableaux_shape5_tail_cols_c01 : (latin_double_three_tail_shape 5).cells := ⟨(0, 1), by decide⟩
def latin_tableaux_shape5_tail_cols_c02 : (latin_double_three_tail_shape 5).cells := ⟨(0, 2), by decide⟩
def latin_tableaux_shape5_tail_cols_c03 : (latin_double_three_tail_shape 5).cells := ⟨(0, 3), by decide⟩
def latin_tableaux_shape5_tail_cols_c04 : (latin_double_three_tail_shape 5).cells := ⟨(0, 4), by decide⟩

def latin_tableaux_shape5_tail_cols_c10 : (latin_double_three_tail_shape 5).cells := ⟨(1, 0), by decide⟩
def latin_tableaux_shape5_tail_cols_c11 : (latin_double_three_tail_shape 5).cells := ⟨(1, 1), by decide⟩
def latin_tableaux_shape5_tail_cols_c12 : (latin_double_three_tail_shape 5).cells := ⟨(1, 2), by decide⟩
def latin_tableaux_shape5_tail_cols_c13 : (latin_double_three_tail_shape 5).cells := ⟨(1, 3), by decide⟩

def latin_tableaux_shape5_tail_cols_c20 : (latin_double_three_tail_shape 5).cells := ⟨(2, 0), by decide⟩
def latin_tableaux_shape5_tail_cols_c21 : (latin_double_three_tail_shape 5).cells := ⟨(2, 1), by decide⟩
def latin_tableaux_shape5_tail_cols_c22 : (latin_double_three_tail_shape 5).cells := ⟨(2, 2), by decide⟩

def latin_tableaux_shape5_tail_cols_c30 : (latin_double_three_tail_shape 5).cells := ⟨(3, 0), by decide⟩
def latin_tableaux_shape5_tail_cols_c31 : (latin_double_three_tail_shape 5).cells := ⟨(3, 1), by decide⟩
def latin_tableaux_shape5_tail_cols_c32 : (latin_double_three_tail_shape 5).cells := ⟨(3, 2), by decide⟩

lemma latin_tableaux_shape5_tail_cols_cells_col4 (c : (latin_double_three_tail_shape 5).cells) :
    c.val.2 = 4 ↔ c.val = (0, 4) := by
  obtain ⟨⟨i, j⟩, hc⟩ := c
  dsimp
  have hc' : (i, j) ∈ latin_double_three_tail_shape 5 := hc
  rw [mem_latin_double_three_tail_shape] at hc'
  obtain ⟨hi, hj⟩ := hc'
  constructor
  · intro h4
    subst h4
    have hi0 : i = 0 := by omega
    subst hi0
    rfl
  · intro h
    exact congr_arg Prod.snd h

lemma latin_tableaux_shape5_tail_cols_cells_col3 (c : (latin_double_three_tail_shape 5).cells) :
    c.val.2 = 3 ↔ c.val = (0, 3) ∨ c.val = (1, 3) := by
  obtain ⟨⟨i, j⟩, hc⟩ := c
  dsimp
  have hc' : (i, j) ∈ latin_double_three_tail_shape 5 := hc
  rw [mem_latin_double_three_tail_shape] at hc'
  obtain ⟨hi, hj⟩ := hc'
  constructor
  · intro h3
    subst h3
    have hi_cases : i = 0 ∨ i = 1 := by omega
    rcases hi_cases with rfl | rfl
    · left; rfl
    · right; rfl
  · rintro (h | h)
    · exact congr_arg Prod.snd h
    · exact congr_arg Prod.snd h

lemma latin_tableaux_shape5_tail_cols_col4_eq (T : (latin_double_three_tail_shape 5).cells → ℕ) :
    latin_column_symbols (latin_double_three_tail_shape 5) T 4 = {T latin_tableaux_shape5_tail_cols_c04} := by
  ext x
  rw [mem_latin_column_symbols, mem_singleton]
  constructor
  · rintro ⟨c, hc4, rfl⟩
    have hc := (latin_tableaux_shape5_tail_cols_cells_col4 c).mp hc4
    apply congr_arg T
    exact Subtype.ext hc
  · rintro rfl
    exact ⟨latin_tableaux_shape5_tail_cols_c04, rfl, rfl⟩

lemma latin_tableaux_shape5_tail_cols_col3_eq (T : (latin_double_three_tail_shape 5).cells → ℕ) :
    latin_column_symbols (latin_double_three_tail_shape 5) T 3 =
      {T latin_tableaux_shape5_tail_cols_c03, T latin_tableaux_shape5_tail_cols_c13} := by
  ext x
  rw [mem_latin_column_symbols, mem_insert, mem_singleton]
  constructor
  · rintro ⟨c, hc3, rfl⟩
    have hc := (latin_tableaux_shape5_tail_cols_cells_col3 c).mp hc3
    rcases hc with h | h
    · left; apply congr_arg T; exact Subtype.ext h
    · right; apply congr_arg T; exact Subtype.ext h
  · rintro (rfl | rfl)
    · exact ⟨latin_tableaux_shape5_tail_cols_c03, rfl, rfl⟩
    · exact ⟨latin_tableaux_shape5_tail_cols_c13, rfl, rfl⟩

lemma latin_tableaux_shape5_tail_cols_rowLen_0 : (latin_double_three_tail_shape 5).rowLen 0 = 5 := by
  rw [latin_double_three_tail_shape_rowLen]; rfl
lemma latin_tableaux_shape5_tail_cols_rowLen_1 : (latin_double_three_tail_shape 5).rowLen 1 = 4 := by
  rw [latin_double_three_tail_shape_rowLen]; rfl
lemma latin_tableaux_shape5_tail_cols_rowLen_2 : (latin_double_three_tail_shape 5).rowLen 2 = 3 := by
  rw [latin_double_three_tail_shape_rowLen]; rfl
lemma latin_tableaux_shape5_tail_cols_rowLen_3 : (latin_double_three_tail_shape 5).rowLen 3 = 3 := by
  rw [latin_double_three_tail_shape_rowLen]; rfl

lemma latin_tableaux_shape5_tail_cols_hT_bounds (T : (latin_double_three_tail_shape 5).cells → ℕ)
    (hT : T ∈ latin_tableaux (latin_double_three_tail_shape 5)) (c : (latin_double_three_tail_shape 5).cells) :
    T c ∈ Finset.Icc 1 ((latin_double_three_tail_shape 5).rowLen c.val.1) := by
  rw [latin_tableaux, Finset.mem_filter] at hT
  have hpi := hT.1
  rw [Fintype.mem_piFinset] at hpi
  exact hpi c

lemma latin_tableaux_shape5_tail_cols_bound_0 (T : (latin_double_three_tail_shape 5).cells → ℕ)
    (hT : T ∈ latin_tableaux (latin_double_three_tail_shape 5)) (c : (latin_double_three_tail_shape 5).cells)
    (hc : c.val.1 = 0) : T c ∈ Finset.Icc 1 5 := by
  have h := latin_tableaux_shape5_tail_cols_hT_bounds T hT c
  rw [hc, latin_tableaux_shape5_tail_cols_rowLen_0] at h
  exact h

lemma latin_tableaux_shape5_tail_cols_bound_1 (T : (latin_double_three_tail_shape 5).cells → ℕ)
    (hT : T ∈ latin_tableaux (latin_double_three_tail_shape 5)) (c : (latin_double_three_tail_shape 5).cells)
    (hc : c.val.1 = 1) : T c ∈ Finset.Icc 1 4 := by
  have h := latin_tableaux_shape5_tail_cols_hT_bounds T hT c
  rw [hc, latin_tableaux_shape5_tail_cols_rowLen_1] at h
  exact h

lemma latin_tableaux_shape5_tail_cols_bound_2 (T : (latin_double_three_tail_shape 5).cells → ℕ)
    (hT : T ∈ latin_tableaux (latin_double_three_tail_shape 5)) (c : (latin_double_three_tail_shape 5).cells)
    (hc : c.val.1 = 2) : T c ∈ Finset.Icc 1 3 := by
  have h := latin_tableaux_shape5_tail_cols_hT_bounds T hT c
  rw [hc, latin_tableaux_shape5_tail_cols_rowLen_2] at h
  exact h

lemma latin_tableaux_shape5_tail_cols_bound_3 (T : (latin_double_three_tail_shape 5).cells → ℕ)
    (hT : T ∈ latin_tableaux (latin_double_three_tail_shape 5)) (c : (latin_double_three_tail_shape 5).cells)
    (hc : c.val.1 = 3) : T c ∈ Finset.Icc 1 3 := by
  have h := latin_tableaux_shape5_tail_cols_hT_bounds T hT c
  rw [hc, latin_tableaux_shape5_tail_cols_rowLen_3] at h
  exact h

lemma latin_tableaux_shape5_tail_cols_hrow {T : (latin_double_three_tail_shape 5).cells → ℕ}
    (hT : T ∈ latin_tableaux (latin_double_three_tail_shape 5))
    (c₁ c₂ : (latin_double_three_tail_shape 5).cells) (h1 : c₁.val.1 = c₂.val.1) (h2 : c₁.val.2 ≠ c₂.val.2) :
    T c₁ ≠ T c₂ := by
  rw [latin_tableaux, Finset.mem_filter] at hT
  intro heq
  exact h2 (hT.2.1 c₁ c₂ h1 heq)

lemma latin_tableaux_shape5_tail_cols_hcol {T : (latin_double_three_tail_shape 5).cells → ℕ}
    (hT : T ∈ latin_tableaux (latin_double_three_tail_shape 5))
    (c₁ c₂ : (latin_double_three_tail_shape 5).cells) (h2 : c₁.val.2 = c₂.val.2) (h1 : c₁.val.1 ≠ c₂.val.1) :
    T c₁ ≠ T c₂ := by
  rw [latin_tableaux, Finset.mem_filter] at hT
  intro heq
  exact h1 (hT.2.2 c₁ c₂ h2 heq)

lemma latin_tableaux_shape5_tail_cols_col_has_ge_4 (a b c d : ℕ)
    (ha : a ∈ Finset.Icc 1 5) (hb : b ∈ Finset.Icc 1 4)
    (hc : c ∈ Finset.Icc 1 3) (hd : d ∈ Finset.Icc 1 3)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    a ≥ 4 ∨ b = 4 := by
  rw [Finset.mem_Icc] at ha hb hc hd
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨hc1, hc2⟩ := hc
  obtain ⟨hd1, hd2⟩ := hd
  interval_cases c <;> interval_cases d <;> interval_cases b <;> interval_cases a <;>
    first | contradiction | omega

lemma latin_tableaux_shape5_tail_cols_at_least_two_ge_4 (p0 p1 p2 q0 q1 q2 : Prop)
    (h0 : p0 ∨ q0) (h1 : p1 ∨ q1) (h2 : p2 ∨ q2)
    (hq01 : ¬ (q0 ∧ q1)) (hq02 : ¬ (q0 ∧ q2)) (hq12 : ¬ (q1 ∧ q2)) :
    (p0 ∧ p1) ∨ (p0 ∧ p2) ∨ (p1 ∧ p2) := by
  tauto

lemma latin_tableaux_shape5_tail_cols_at_most_two_ge_4 (x0 x1 x2 x3 x4 : ℕ)
    (h0 : x0 ∈ Finset.Icc 1 5) (h1 : x1 ∈ Finset.Icc 1 5) (h2 : x2 ∈ Finset.Icc 1 5)
    (h3 : x3 ∈ Finset.Icc 1 5) (h4 : x4 ∈ Finset.Icc 1 5)
    (d01 : x0 ≠ x1) (d02 : x0 ≠ x2) (d03 : x0 ≠ x3) (d04 : x0 ≠ x4)
    (d12 : x1 ≠ x2) (d13 : x1 ≠ x3) (d14 : x1 ≠ x4)
    (d23 : x2 ≠ x3) (d24 : x2 ≠ x4) (d34 : x3 ≠ x4)
    (hge : (x0 ≥ 4 ∧ x1 ≥ 4) ∨ (x0 ≥ 4 ∧ x2 ≥ 4) ∨ (x1 ≥ 4 ∧ x2 ≥ 4)) :
    x3 ≤ 3 ∧ x4 ≤ 3 := by
  rw [Finset.mem_Icc] at h0 h1 h2 h3 h4
  obtain ⟨h0a, h0b⟩ := h0
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  obtain ⟨h3a, h3b⟩ := h3
  obtain ⟨h4a, h4b⟩ := h4
  rcases hge with ⟨g0, g1⟩ | ⟨g0, g2⟩ | ⟨g1, g2⟩
  · interval_cases x0 <;> interval_cases x1 <;>
      (try contradiction) <;>
      (interval_cases x3 <;> interval_cases x4 <;> first | contradiction | omega)
  · interval_cases x0 <;> interval_cases x2 <;>
      (try contradiction) <;>
      (interval_cases x3 <;> interval_cases x4 <;> first | contradiction | omega)
  · interval_cases x1 <;> interval_cases x2 <;>
      (try contradiction) <;>
      (interval_cases x3 <;> interval_cases x4 <;> first | contradiction | omega)

lemma latin_tableaux_shape5_tail_cols_not_three_ge_4 (x0 x1 x2 : ℕ)
    (h0 : x0 ∈ Finset.Icc 1 5) (h1 : x1 ∈ Finset.Icc 1 5) (h2 : x2 ∈ Finset.Icc 1 5)
    (d01 : x0 ≠ x1) (d02 : x0 ≠ x2) (d12 : x1 ≠ x2)
    (g0 : x0 ≥ 4) (g1 : x1 ≥ 4) (g2 : x2 ≥ 4) : False := by
  rw [Finset.mem_Icc] at h0 h1 h2
  obtain ⟨h0a, h0b⟩ := h0
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  interval_cases x0 <;> interval_cases x1 <;> interval_cases x2 <;> contradiction

lemma latin_tableaux_shape5_tail_cols_three_cols_pigeonhole (p0 p1 p2 q0 q1 q2 : Prop)
    (hp01 : ¬ (p0 ∧ p1)) (hp02 : ¬ (p0 ∧ p2)) (hp12 : ¬ (p1 ∧ p2))
    (hq01 : ¬ (q0 ∧ q1)) (hq02 : ¬ (q0 ∧ q2)) (hq12 : ¬ (q1 ∧ q2)) :
    (¬ p0 ∧ ¬ q0) ∨ (¬ p1 ∧ ¬ q1) ∨ (¬ p2 ∧ ¬ q2) := by
  tauto

lemma latin_tableaux_shape5_tail_cols_col_missing_s (s a b c d : ℕ)
    (hs : s ∈ Finset.Icc 1 3)
    (ha : a ∈ Finset.Icc 1 5) (hb : b ∈ Finset.Icc 1 4)
    (hc : c ∈ Finset.Icc 1 3) (hd : d ∈ Finset.Icc 1 3)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (has : a ≠ s) (hbs : b ≠ s) (hcs : c ≠ s) (hds : d ≠ s) :
    a = 5 ∧ b = 4 := by
  rw [Finset.mem_Icc] at hs ha hb hc hd
  obtain ⟨hs1, hs2⟩ := hs
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨hc1, hc2⟩ := hc
  obtain ⟨hd1, hd2⟩ := hd
  interval_cases s <;> interval_cases c <;> interval_cases d <;>
    (try contradiction) <;>
    interval_cases b <;> interval_cases a <;>
    first | contradiction | omega

lemma latin_tableaux_shape5_tail_cols_case_j_star (x0 x1 x2 y0 y1 y2 : ℕ)
    (h0 : x0 ∈ Finset.Icc 1 5) (h1 : x1 ∈ Finset.Icc 1 5) (h2 : x2 ∈ Finset.Icc 1 5)
    (d01 : x0 ≠ x1) (d02 : x0 ≠ x2) (_d12 : x1 ≠ x2)
    (dy01 : y0 ≠ y1) (dy02 : y0 ≠ y2) (dy12 : y1 ≠ y2)
    (h0_ge : x0 ≥ 4 ∨ y0 = 4)
    (h1_ge : x1 ≥ 4 ∨ y1 = 4)
    (h2_ge : x2 ≥ 4 ∨ y2 = 4)
    (h_star : (x0 = 5 ∧ y0 = 4) ∨ (x1 = 5 ∧ y1 = 4) ∨ (x2 = 5 ∧ y2 = 4)) : False := by
  have g0 : x0 ≥ 4 := by
    rcases h_star with ⟨h, -⟩ | ⟨-, hy1⟩ | ⟨-, hy2⟩
    · omega
    · rcases h0_ge with h | h; exact h; subst hy1; exact (dy01 h).elim
    · rcases h0_ge with h | h; exact h; subst hy2; exact (dy02 h).elim
  have g1 : x1 ≥ 4 := by
    rcases h_star with ⟨-, hy0⟩ | ⟨h, -⟩ | ⟨-, hy2⟩
    · rcases h1_ge with h | h; exact h; subst hy0; exact (dy01.symm h).elim
    · omega
    · rcases h1_ge with h | h; exact h; subst hy2; exact (dy12 h).elim
  have g2 : x2 ≥ 4 := by
    rcases h_star with ⟨-, hy0⟩ | ⟨-, hy1⟩ | ⟨h, -⟩
    · rcases h2_ge with h | h; exact h; subst hy0; exact (dy02.symm h).elim
    · rcases h2_ge with h | h; exact h; subst hy1; exact (dy12.symm h).elim
    · omega
  rw [Finset.mem_Icc] at h0 h1 h2
  obtain ⟨h0a, h0b⟩ := h0
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  interval_cases x0 <;> interval_cases x1 <;> interval_cases x2 <;> contradiction

lemma latin_tableaux_shape5_tail_cols_two_in_three_without_s (s a b : ℕ)
    (hs : s ∈ Finset.Icc 1 3)
    (ha : a ∈ Finset.Icc 1 3) (hb : b ∈ Finset.Icc 1 3)
    (hab : a ≠ b) (has : a ≠ s) (hbs : b ≠ s) :
    {a, b} = Finset.Icc 1 3 \ {s} := by
  rw [Finset.mem_Icc] at hs ha hb
  obtain ⟨hs1, hs2⟩ := hs
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  interval_cases s <;> interval_cases a <;> interval_cases b <;>
    first | contradiction | decide

/-- Columns 3 and 4 of any Latin tableau of shape (5,4,3,3) partition {1,2,3} into a pair and a singleton. -/
theorem latin_tableaux_shape5_tail_cols :
  ∀ T ∈ latin_tableaux (latin_double_three_tail_shape 5),
    ∃ s ∈ Finset.Icc 1 3,
      latin_column_symbols (latin_double_three_tail_shape 5) T 4 = {s} ∧
      latin_column_symbols (latin_double_three_tail_shape 5) T 3 = Finset.Icc 1 3 \ {s} := by
  intro T hT
  let c00 := latin_tableaux_shape5_tail_cols_c00
  let c01 := latin_tableaux_shape5_tail_cols_c01
  let c02 := latin_tableaux_shape5_tail_cols_c02
  let c03 := latin_tableaux_shape5_tail_cols_c03
  let c04 := latin_tableaux_shape5_tail_cols_c04
  let c10 := latin_tableaux_shape5_tail_cols_c10
  let c11 := latin_tableaux_shape5_tail_cols_c11
  let c12 := latin_tableaux_shape5_tail_cols_c12
  let c13 := latin_tableaux_shape5_tail_cols_c13
  let c20 := latin_tableaux_shape5_tail_cols_c20
  let c21 := latin_tableaux_shape5_tail_cols_c21
  let c22 := latin_tableaux_shape5_tail_cols_c22
  let c30 := latin_tableaux_shape5_tail_cols_c30
  let c31 := latin_tableaux_shape5_tail_cols_c31
  let c32 := latin_tableaux_shape5_tail_cols_c32
  have hb00 := latin_tableaux_shape5_tail_cols_bound_0 T hT c00 rfl
  have hb01 := latin_tableaux_shape5_tail_cols_bound_0 T hT c01 rfl
  have hb02 := latin_tableaux_shape5_tail_cols_bound_0 T hT c02 rfl
  have hb03 := latin_tableaux_shape5_tail_cols_bound_0 T hT c03 rfl
  have hb04 := latin_tableaux_shape5_tail_cols_bound_0 T hT c04 rfl
  have hb10 := latin_tableaux_shape5_tail_cols_bound_1 T hT c10 rfl
  have hb11 := latin_tableaux_shape5_tail_cols_bound_1 T hT c11 rfl
  have hb12 := latin_tableaux_shape5_tail_cols_bound_1 T hT c12 rfl
  have hb13 := latin_tableaux_shape5_tail_cols_bound_1 T hT c13 rfl
  have hb20 := latin_tableaux_shape5_tail_cols_bound_2 T hT c20 rfl
  have hb21 := latin_tableaux_shape5_tail_cols_bound_2 T hT c21 rfl
  have hb22 := latin_tableaux_shape5_tail_cols_bound_2 T hT c22 rfl
  have hb30 := latin_tableaux_shape5_tail_cols_bound_3 T hT c30 rfl
  have hb31 := latin_tableaux_shape5_tail_cols_bound_3 T hT c31 rfl
  have hb32 := latin_tableaux_shape5_tail_cols_bound_3 T hT c32 rfl
  have d0_01 : T c00 ≠ T c01 := latin_tableaux_shape5_tail_cols_hrow hT _ _ rfl (by decide)
  have d0_02 : T c00 ≠ T c02 := latin_tableaux_shape5_tail_cols_hrow hT _ _ rfl (by decide)
  have d0_03 : T c00 ≠ T c03 := latin_tableaux_shape5_tail_cols_hrow hT _ _ rfl (by decide)
  have d0_04 : T c00 ≠ T c04 := latin_tableaux_shape5_tail_cols_hrow hT _ _ rfl (by decide)
  have d0_12 : T c01 ≠ T c02 := latin_tableaux_shape5_tail_cols_hrow hT _ _ rfl (by decide)
  have d0_13 : T c01 ≠ T c03 := latin_tableaux_shape5_tail_cols_hrow hT _ _ rfl (by decide)
  have d0_14 : T c01 ≠ T c04 := latin_tableaux_shape5_tail_cols_hrow hT _ _ rfl (by decide)
  have d0_23 : T c02 ≠ T c03 := latin_tableaux_shape5_tail_cols_hrow hT _ _ rfl (by decide)
  have d0_24 : T c02 ≠ T c04 := latin_tableaux_shape5_tail_cols_hrow hT _ _ rfl (by decide)
  have d0_34 : T c03 ≠ T c04 := latin_tableaux_shape5_tail_cols_hrow hT _ _ rfl (by decide)
  have d1_01 : T c10 ≠ T c11 := latin_tableaux_shape5_tail_cols_hrow hT _ _ rfl (by decide)
  have d1_02 : T c10 ≠ T c12 := latin_tableaux_shape5_tail_cols_hrow hT _ _ rfl (by decide)
  have d1_03 : T c10 ≠ T c13 := latin_tableaux_shape5_tail_cols_hrow hT _ _ rfl (by decide)
  have d1_12 : T c11 ≠ T c12 := latin_tableaux_shape5_tail_cols_hrow hT _ _ rfl (by decide)
  have d1_13 : T c11 ≠ T c13 := latin_tableaux_shape5_tail_cols_hrow hT _ _ rfl (by decide)
  have d1_23 : T c12 ≠ T c13 := latin_tableaux_shape5_tail_cols_hrow hT _ _ rfl (by decide)
  have d2_01 : T c20 ≠ T c21 := latin_tableaux_shape5_tail_cols_hrow hT _ _ rfl (by decide)
  have d2_02 : T c20 ≠ T c22 := latin_tableaux_shape5_tail_cols_hrow hT _ _ rfl (by decide)
  have d2_12 : T c21 ≠ T c22 := latin_tableaux_shape5_tail_cols_hrow hT _ _ rfl (by decide)
  have d3_01 : T c30 ≠ T c31 := latin_tableaux_shape5_tail_cols_hrow hT _ _ rfl (by decide)
  have d3_02 : T c30 ≠ T c32 := latin_tableaux_shape5_tail_cols_hrow hT _ _ rfl (by decide)
  have d3_12 : T c31 ≠ T c32 := latin_tableaux_shape5_tail_cols_hrow hT _ _ rfl (by decide)
  have dc0_01 : T c00 ≠ T c10 := latin_tableaux_shape5_tail_cols_hcol hT _ _ rfl (by decide)
  have dc0_02 : T c00 ≠ T c20 := latin_tableaux_shape5_tail_cols_hcol hT _ _ rfl (by decide)
  have dc0_03 : T c00 ≠ T c30 := latin_tableaux_shape5_tail_cols_hcol hT _ _ rfl (by decide)
  have dc0_12 : T c10 ≠ T c20 := latin_tableaux_shape5_tail_cols_hcol hT _ _ rfl (by decide)
  have dc0_13 : T c10 ≠ T c30 := latin_tableaux_shape5_tail_cols_hcol hT _ _ rfl (by decide)
  have dc0_23 : T c20 ≠ T c30 := latin_tableaux_shape5_tail_cols_hcol hT _ _ rfl (by decide)
  have dc1_01 : T c01 ≠ T c11 := latin_tableaux_shape5_tail_cols_hcol hT _ _ rfl (by decide)
  have dc1_02 : T c01 ≠ T c21 := latin_tableaux_shape5_tail_cols_hcol hT _ _ rfl (by decide)
  have dc1_03 : T c01 ≠ T c31 := latin_tableaux_shape5_tail_cols_hcol hT _ _ rfl (by decide)
  have dc1_12 : T c11 ≠ T c21 := latin_tableaux_shape5_tail_cols_hcol hT _ _ rfl (by decide)
  have dc1_13 : T c11 ≠ T c31 := latin_tableaux_shape5_tail_cols_hcol hT _ _ rfl (by decide)
  have dc1_23 : T c21 ≠ T c31 := latin_tableaux_shape5_tail_cols_hcol hT _ _ rfl (by decide)
  have dc2_01 : T c02 ≠ T c12 := latin_tableaux_shape5_tail_cols_hcol hT _ _ rfl (by decide)
  have dc2_02 : T c02 ≠ T c22 := latin_tableaux_shape5_tail_cols_hcol hT _ _ rfl (by decide)
  have dc2_03 : T c02 ≠ T c32 := latin_tableaux_shape5_tail_cols_hcol hT _ _ rfl (by decide)
  have dc2_12 : T c12 ≠ T c22 := latin_tableaux_shape5_tail_cols_hcol hT _ _ rfl (by decide)
  have dc2_13 : T c12 ≠ T c32 := latin_tableaux_shape5_tail_cols_hcol hT _ _ rfl (by decide)
  have dc2_23 : T c22 ≠ T c32 := latin_tableaux_shape5_tail_cols_hcol hT _ _ rfl (by decide)
  have dc3_01 : T c03 ≠ T c13 := latin_tableaux_shape5_tail_cols_hcol hT _ _ rfl (by decide)
  have h0_ge := latin_tableaux_shape5_tail_cols_col_has_ge_4 (T c00) (T c10) (T c20) (T c30)
    hb00 hb10 hb20 hb30 dc0_01 dc0_02 dc0_03 dc0_12 dc0_13 dc0_23
  have h1_ge := latin_tableaux_shape5_tail_cols_col_has_ge_4 (T c01) (T c11) (T c21) (T c31)
    hb01 hb11 hb21 hb31 dc1_01 dc1_02 dc1_03 dc1_12 dc1_13 dc1_23
  have h2_ge := latin_tableaux_shape5_tail_cols_col_has_ge_4 (T c02) (T c12) (T c22) (T c32)
    hb02 hb12 hb22 hb32 dc2_01 dc2_02 dc2_03 dc2_12 dc2_13 dc2_23
  have hq01 : ¬ (T c10 = 4 ∧ T c11 = 4) := fun ⟨h1, h2⟩ => d1_01 (h1.trans h2.symm)
  have hq02 : ¬ (T c10 = 4 ∧ T c12 = 4) := fun ⟨h1, h2⟩ => d1_02 (h1.trans h2.symm)
  have hq12 : ¬ (T c11 = 4 ∧ T c12 = 4) := fun ⟨h1, h2⟩ => d1_12 (h1.trans h2.symm)
  have hge := latin_tableaux_shape5_tail_cols_at_least_two_ge_4 (T c00 ≥ 4) (T c01 ≥ 4) (T c02 ≥ 4)
    (T c10 = 4) (T c11 = 4) (T c12 = 4) h0_ge h1_ge h2_ge hq01 hq02 hq12
  have ⟨_h03_le, _h04_le⟩ := latin_tableaux_shape5_tail_cols_at_most_two_ge_4 (T c00) (T c01) (T c02) (T c03) (T c04)
    hb00 hb01 hb02 hb03 hb04 d0_01 d0_02 d0_03 d0_04 d0_12 d0_13 d0_14 d0_23 d0_24 d0_34 hge
  have hs_icc : T c04 ∈ Finset.Icc 1 3 := by
    rw [Finset.mem_Icc] at hb04 ⊢; omega
  have h03_icc : T c03 ∈ Finset.Icc 1 3 := by
    rw [Finset.mem_Icc] at hb03 ⊢; omega
  have _h13_ne_4 : T c13 ≠ 4 := by
    intro h4
    have hy0 : T c10 ≠ 4 := fun h => d1_03 (h.trans h4.symm)
    have hy1 : T c11 ≠ 4 := fun h => d1_13 (h.trans h4.symm)
    have hy2 : T c12 ≠ 4 := fun h => d1_23 (h.trans h4.symm)
    have g0 : T c00 ≥ 4 := by rcases h0_ge with h | h; exact h; exact (hy0 h).elim
    have g1 : T c01 ≥ 4 := by rcases h1_ge with h | h; exact h; exact (hy1 h).elim
    have g2 : T c02 ≥ 4 := by rcases h2_ge with h | h; exact h; exact (hy2 h).elim
    exact latin_tableaux_shape5_tail_cols_not_three_ge_4 (T c00) (T c01) (T c02)
      hb00 hb01 hb02 d0_01 d0_02 d0_12 g0 g1 g2
  have h13_icc : T c13 ∈ Finset.Icc 1 3 := by
    rw [Finset.mem_Icc] at hb13 ⊢; omega
  have hp01 : ¬ (T c20 = T c04 ∧ T c21 = T c04) := fun ⟨h1, h2⟩ => d2_01 (h1.trans h2.symm)
  have hp02 : ¬ (T c20 = T c04 ∧ T c22 = T c04) := fun ⟨h1, h2⟩ => d2_02 (h1.trans h2.symm)
  have hp12 : ¬ (T c21 = T c04 ∧ T c22 = T c04) := fun ⟨h1, h2⟩ => d2_12 (h1.trans h2.symm)
  have hrq01 : ¬ (T c30 = T c04 ∧ T c31 = T c04) := fun ⟨h1, h2⟩ => d3_01 (h1.trans h2.symm)
  have hrq02 : ¬ (T c30 = T c04 ∧ T c32 = T c04) := fun ⟨h1, h2⟩ => d3_02 (h1.trans h2.symm)
  have hrq12 : ¬ (T c31 = T c04 ∧ T c32 = T c04) := fun ⟨h1, h2⟩ => d3_12 (h1.trans h2.symm)
  have hpig := latin_tableaux_shape5_tail_cols_three_cols_pigeonhole
    (T c20 = T c04) (T c21 = T c04) (T c22 = T c04)
    (T c30 = T c04) (T c31 = T c04) (T c32 = T c04)
    hp01 hp02 hp12 hrq01 hrq02 hrq12
  have h13_ne_s : T c13 ≠ T c04 := by
    intro heq_s
    have h_star : (T c00 = 5 ∧ T c10 = 4) ∨ (T c01 = 5 ∧ T c11 = 4) ∨ (T c02 = 5 ∧ T c12 = 4) := by
      rcases hpig with ⟨h20, h30⟩ | ⟨h21, h31⟩ | ⟨h22, h32⟩
      · left
        have has : T c00 ≠ T c04 := d0_04
        have hbs : T c10 ≠ T c04 := fun h => d1_03 (h.trans heq_s.symm)
        exact latin_tableaux_shape5_tail_cols_col_missing_s (T c04) (T c00) (T c10) (T c20) (T c30)
          hs_icc hb00 hb10 hb20 hb30 dc0_01 dc0_02 dc0_03 dc0_12 dc0_13 dc0_23 has hbs h20 h30
      · right; left
        have has : T c01 ≠ T c04 := d0_14
        have hbs : T c11 ≠ T c04 := fun h => d1_13 (h.trans heq_s.symm)
        exact latin_tableaux_shape5_tail_cols_col_missing_s (T c04) (T c01) (T c11) (T c21) (T c31)
          hs_icc hb01 hb11 hb21 hb31 dc1_01 dc1_02 dc1_03 dc1_12 dc1_13 dc1_23 has hbs h21 h31
      · right; right
        have has : T c02 ≠ T c04 := d0_24
        have hbs : T c12 ≠ T c04 := fun h => d1_23 (h.trans heq_s.symm)
        exact latin_tableaux_shape5_tail_cols_col_missing_s (T c04) (T c02) (T c12) (T c22) (T c32)
          hs_icc hb02 hb12 hb22 hb32 dc2_01 dc2_02 dc2_03 dc2_12 dc2_13 dc2_23 has hbs h22 h32
    exact latin_tableaux_shape5_tail_cols_case_j_star (T c00) (T c01) (T c02) (T c10) (T c11) (T c12)
      hb00 hb01 hb02 d0_01 d0_02 d0_12 d1_01 d1_02 d1_12 h0_ge h1_ge h2_ge h_star
  refine ⟨T c04, hs_icc, ?_, ?_⟩
  · exact latin_tableaux_shape5_tail_cols_col4_eq T
  · rw [latin_tableaux_shape5_tail_cols_col3_eq T]
    exact latin_tableaux_shape5_tail_cols_two_in_three_without_s (T c04) (T c03) (T c13)
      hs_icc h03_icc h13_icc dc3_01 d0_34 h13_ne_s
