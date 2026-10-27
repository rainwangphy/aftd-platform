import AFTD.Prelude
import AFTD.Kb.Tcs.LatinDoubleThreeTailShape
import AFTD.Kb.Tcs.LatinTableauxCount
import AFTD.Kb.Tcs.LatinDoubleThreeTailProfileBase
import AFTD.Kb.Tcs.LatinTableaux
import AFTD.Kb.Tcs.LatinDoubleThreeTailShapeRowLen
import AFTD.Kb.Tcs.MemLatinDoubleThreeTailShape

/-!
# latin_double_three_tail_count_base

Topic: combinatorics   Node: b4cff1dd4510

Provenance: helper lemma. Helper for the open enumeration problem in https://arxiv.org/html/2610.29291v1, Conjecture 6.3, using the availability-permanent identity of Lemma 5.4. Exact computational route: experiments 4100, 4103 and 4106.

There are exactly 144 Latin tableaux of shape (5,4,3,3).
-/

def latin_dtt_base_colok (a b : List ℕ) : Bool := (List.zip a b).all (fun p => p.1 != p.2)

def latin_dtt_base_gen : List (List ℕ × List ℕ × List ℕ × List ℕ) :=
  (List.permutations' [1,2,3,4,5]).flatMap fun r0 =>
  ((List.permutations' [1,2,3,4]).filter (fun r1 => latin_dtt_base_colok r0 r1)).flatMap fun r1 =>
  ((List.permutations' [1,2,3]).filter (fun r2 => latin_dtt_base_colok r0 r2 && latin_dtt_base_colok r1 r2)).flatMap fun r2 =>
  ((List.permutations' [1,2,3]).filter
    (fun r3 => latin_dtt_base_colok r0 r3 && latin_dtt_base_colok r1 r3 && latin_dtt_base_colok r2 r3)).map fun r3 => (r0, r1, r2, r3)

def latin_dtt_base_row (x : List ℕ × List ℕ × List ℕ × List ℕ) : ℕ → List ℕ
  | 0 => x.1
  | 1 => x.2.1
  | 2 => x.2.2.1
  | _ => x.2.2.2

def latin_dtt_base_len (i : ℕ) : ℕ := if i < 4 then max 3 (5 - i) else 0

def latin_dtt_base_chk (x : List ℕ × List ℕ × List ℕ × List ℕ) : Bool :=
  (List.range 4).all fun i => ((latin_dtt_base_row x i).length == latin_dtt_base_len i) &&
    (List.range (latin_dtt_base_len i)).all fun j =>
      decide (1 ≤ (latin_dtt_base_row x i).getD j 0) && decide ((latin_dtt_base_row x i).getD j 0 ≤ latin_dtt_base_len i) &&
      (List.range (latin_dtt_base_len i)).all (fun j' => (latin_dtt_base_row x i).getD j 0 != (latin_dtt_base_row x i).getD j' 0 || j == j') &&
      (List.range 4).all (fun i' => !(decide (j < latin_dtt_base_len i')) ||
        (latin_dtt_base_row x i).getD j 0 != (latin_dtt_base_row x i').getD j 0 || i == i')

set_option maxRecDepth 100000 in
theorem latin_dtt_base_gen_length : latin_dtt_base_gen.length = 144 := by decide +kernel

set_option maxRecDepth 100000 in
theorem latin_dtt_base_gen_nodup : latin_dtt_base_gen.Nodup := by decide +kernel

set_option maxRecDepth 100000 in
theorem latin_dtt_base_gen_chk : ∀ x ∈ latin_dtt_base_gen, latin_dtt_base_chk x = true := by decide +kernel

theorem latin_dtt_base_perm (l t : List ℕ) (hl : l.Nodup) (hs : ∀ x ∈ l, x ∈ t) (hlen : t.length ≤ l.length) :
    l.Perm t :=
  (hl.subperm hs).perm_of_length_le hlen

theorem latin_dtt_base_perm5 (x0 x1 x2 x3 x4 : ℕ) (h0 : 1 ≤ x0 ∧ x0 ≤ 5) (h1 : 1 ≤ x1 ∧ x1 ≤ 5) (h2 : 1 ≤ x2 ∧ x2 ≤ 5) (h3 : 1 ≤ x3 ∧ x3 ≤ 5) (h4 : 1 ≤ x4 ∧ x4 ≤ 5) (n01 : x0 ≠ x1) (n02 : x0 ≠ x2) (n03 : x0 ≠ x3) (n04 : x0 ≠ x4) (n12 : x1 ≠ x2) (n13 : x1 ≠ x3) (n14 : x1 ≠ x4) (n23 : x2 ≠ x3) (n24 : x2 ≠ x4) (n34 : x3 ≠ x4) :
    ([x0, x1, x2, x3, x4] : List ℕ).Perm [1, 2, 3, 4, 5] := by
  apply latin_dtt_base_perm
  · simp [List.nodup_cons, n01, n02, n03, n04, n12, n13, n14, n23, n24, n34]
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp <;> omega
  · simp

theorem latin_dtt_base_perm4 (x0 x1 x2 x3 : ℕ) (h0 : 1 ≤ x0 ∧ x0 ≤ 4) (h1 : 1 ≤ x1 ∧ x1 ≤ 4) (h2 : 1 ≤ x2 ∧ x2 ≤ 4) (h3 : 1 ≤ x3 ∧ x3 ≤ 4) (n01 : x0 ≠ x1) (n02 : x0 ≠ x2) (n03 : x0 ≠ x3) (n12 : x1 ≠ x2) (n13 : x1 ≠ x3) (n23 : x2 ≠ x3) :
    ([x0, x1, x2, x3] : List ℕ).Perm [1, 2, 3, 4] := by
  apply latin_dtt_base_perm
  · simp [List.nodup_cons, n01, n02, n03, n12, n13, n23]
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp <;> omega
  · simp

theorem latin_dtt_base_perm3 (x0 x1 x2 : ℕ) (h0 : 1 ≤ x0 ∧ x0 ≤ 3) (h1 : 1 ≤ x1 ∧ x1 ≤ 3) (h2 : 1 ≤ x2 ∧ x2 ≤ 3) (n01 : x0 ≠ x1) (n02 : x0 ≠ x2) (n12 : x1 ≠ x2) :
    ([x0, x1, x2] : List ℕ).Perm [1, 2, 3] := by
  apply latin_dtt_base_perm
  · simp [List.nodup_cons, n01, n02, n12]
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp <;> omega
  · simp

theorem latin_dtt_base_fwd (a00 a01 a02 a03 a04 a10 a11 a12 a13 a20 a21 a22 a30 a31 a32 : ℕ)
    (b00 : 1 ≤ a00 ∧ a00 ≤ 5) (b01 : 1 ≤ a01 ∧ a01 ≤ 5) (b02 : 1 ≤ a02 ∧ a02 ≤ 5) (b03 : 1 ≤ a03 ∧ a03 ≤ 5) (b04 : 1 ≤ a04 ∧ a04 ≤ 5) (b10 : 1 ≤ a10 ∧ a10 ≤ 4) (b11 : 1 ≤ a11 ∧ a11 ≤ 4) (b12 : 1 ≤ a12 ∧ a12 ≤ 4) (b13 : 1 ≤ a13 ∧ a13 ≤ 4) (b20 : 1 ≤ a20 ∧ a20 ≤ 3) (b21 : 1 ≤ a21 ∧ a21 ≤ 3) (b22 : 1 ≤ a22 ∧ a22 ≤ 3) (b30 : 1 ≤ a30 ∧ a30 ≤ 3) (b31 : 1 ≤ a31 ∧ a31 ≤ 3) (b32 : 1 ≤ a32 ∧ a32 ≤ 3)
    (n0001 : a00 ≠ a01) (n0002 : a00 ≠ a02) (n0003 : a00 ≠ a03) (n0004 : a00 ≠ a04) (n0010 : a00 ≠ a10) (n0020 : a00 ≠ a20) (n0030 : a00 ≠ a30) (n0102 : a01 ≠ a02) (n0103 : a01 ≠ a03) (n0104 : a01 ≠ a04) (n0111 : a01 ≠ a11) (n0121 : a01 ≠ a21) (n0131 : a01 ≠ a31) (n0203 : a02 ≠ a03) (n0204 : a02 ≠ a04) (n0212 : a02 ≠ a12) (n0222 : a02 ≠ a22) (n0232 : a02 ≠ a32) (n0304 : a03 ≠ a04) (n0313 : a03 ≠ a13) (n1011 : a10 ≠ a11) (n1012 : a10 ≠ a12) (n1013 : a10 ≠ a13) (n1020 : a10 ≠ a20) (n1030 : a10 ≠ a30) (n1112 : a11 ≠ a12) (n1113 : a11 ≠ a13) (n1121 : a11 ≠ a21) (n1131 : a11 ≠ a31) (n1213 : a12 ≠ a13) (n1222 : a12 ≠ a22) (n1232 : a12 ≠ a32) (n2021 : a20 ≠ a21) (n2022 : a20 ≠ a22) (n2030 : a20 ≠ a30) (n2122 : a21 ≠ a22) (n2131 : a21 ≠ a31) (n2232 : a22 ≠ a32) (n3031 : a30 ≠ a31) (n3032 : a30 ≠ a32) (n3132 : a31 ≠ a32) :
    ([a00, a01, a02, a03, a04], [a10, a11, a12, a13], [a20, a21, a22], [a30, a31, a32]) ∈ latin_dtt_base_gen := by
  simp only [latin_dtt_base_gen, List.mem_flatMap, List.mem_filter, List.mem_map, List.mem_permutations']
  exact ⟨[a00, a01, a02, a03, a04], latin_dtt_base_perm5 a00 a01 a02 a03 a04 b00 b01 b02 b03 b04 n0001 n0002 n0003 n0004 n0102 n0103 n0104 n0203 n0204 n0304, [a10, a11, a12, a13], ⟨latin_dtt_base_perm4 a10 a11 a12 a13 b10 b11 b12 b13 n1011 n1012 n1013 n1112 n1113 n1213, by simp [latin_dtt_base_colok, n0010, n0111, n0212, n0313]⟩,
    [a20, a21, a22], ⟨latin_dtt_base_perm3 a20 a21 a22 b20 b21 b22 n2021 n2022 n2122, by simp [latin_dtt_base_colok, n0020, n0121, n0222, n1020, n1121, n1222]⟩, [a30, a31, a32], ⟨latin_dtt_base_perm3 a30 a31 a32 b30 b31 b32 n3031 n3032 n3132, by simp [latin_dtt_base_colok, n0030, n0131, n0232, n1030, n1131, n1232, n2030, n2131, n2232]⟩, rfl⟩

def latin_dtt_base_g (T : (latin_double_three_tail_shape 5).cells → ℕ) (i j : ℕ) : ℕ :=
  if h : (i, j) ∈ (latin_double_three_tail_shape 5).cells then T ⟨(i, j), h⟩ else 0

def latin_dtt_base_F (T : (latin_double_three_tail_shape 5).cells → ℕ) : List ℕ × List ℕ × List ℕ × List ℕ :=
  ((List.range 5).map (latin_dtt_base_g T 0), (List.range 4).map (latin_dtt_base_g T 1), (List.range 3).map (latin_dtt_base_g T 2),
    (List.range 3).map (latin_dtt_base_g T 3))

theorem latin_dtt_base_getD_map_range (f : ℕ → ℕ) (n j : ℕ) (hj : j < n) :
    ((List.range n).map f).getD j 0 = f j := by
  simp [hj]

theorem latin_dtt_base_cell (c : (latin_double_three_tail_shape 5).cells) : c.1.1 < 4 ∧ c.1.2 < latin_dtt_base_len c.1.1 := by
  have h := (mem_latin_double_three_tail_shape 5 c.1.1 c.1.2).1 c.2
  have h4 : c.1.1 < 4 := by omega
  refine ⟨h4, ?_⟩
  simp only [latin_dtt_base_len, if_pos h4]
  exact h.2

theorem latin_dtt_base_mem (i j : ℕ) (hi : i < 4) (hj : j < latin_dtt_base_len i) : (i, j) ∈ (latin_double_three_tail_shape 5).cells := by
  apply (mem_latin_double_three_tail_shape 5 i j).2
  simp only [latin_dtt_base_len, if_pos hi] at hj
  exact ⟨by omega, hj⟩

theorem latin_dtt_base_row_eq (x : List ℕ × List ℕ × List ℕ × List ℕ) :
    x = (latin_dtt_base_row x 0, latin_dtt_base_row x 1, latin_dtt_base_row x 2, latin_dtt_base_row x 3) := rfl

set_option maxHeartbeats 4000000 in
theorem latin_dtt_base_F_mem (T : (latin_double_three_tail_shape 5).cells → ℕ) (hT : T ∈ latin_tableaux (latin_double_three_tail_shape 5)) : latin_dtt_base_F T ∈ latin_dtt_base_gen := by
  simp only [latin_tableaux, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc] at hT
  obtain ⟨hb, hr, hcl⟩ := hT
  have m00 : (0, 0) ∈ (latin_double_three_tail_shape 5).cells := latin_dtt_base_mem 0 0 (by decide) (by decide)
  have m01 : (0, 1) ∈ (latin_double_three_tail_shape 5).cells := latin_dtt_base_mem 0 1 (by decide) (by decide)
  have m02 : (0, 2) ∈ (latin_double_three_tail_shape 5).cells := latin_dtt_base_mem 0 2 (by decide) (by decide)
  have m03 : (0, 3) ∈ (latin_double_three_tail_shape 5).cells := latin_dtt_base_mem 0 3 (by decide) (by decide)
  have m04 : (0, 4) ∈ (latin_double_three_tail_shape 5).cells := latin_dtt_base_mem 0 4 (by decide) (by decide)
  have m10 : (1, 0) ∈ (latin_double_three_tail_shape 5).cells := latin_dtt_base_mem 1 0 (by decide) (by decide)
  have m11 : (1, 1) ∈ (latin_double_three_tail_shape 5).cells := latin_dtt_base_mem 1 1 (by decide) (by decide)
  have m12 : (1, 2) ∈ (latin_double_three_tail_shape 5).cells := latin_dtt_base_mem 1 2 (by decide) (by decide)
  have m13 : (1, 3) ∈ (latin_double_three_tail_shape 5).cells := latin_dtt_base_mem 1 3 (by decide) (by decide)
  have m20 : (2, 0) ∈ (latin_double_three_tail_shape 5).cells := latin_dtt_base_mem 2 0 (by decide) (by decide)
  have m21 : (2, 1) ∈ (latin_double_three_tail_shape 5).cells := latin_dtt_base_mem 2 1 (by decide) (by decide)
  have m22 : (2, 2) ∈ (latin_double_three_tail_shape 5).cells := latin_dtt_base_mem 2 2 (by decide) (by decide)
  have m30 : (3, 0) ∈ (latin_double_three_tail_shape 5).cells := latin_dtt_base_mem 3 0 (by decide) (by decide)
  have m31 : (3, 1) ∈ (latin_double_three_tail_shape 5).cells := latin_dtt_base_mem 3 1 (by decide) (by decide)
  have m32 : (3, 2) ∈ (latin_double_three_tail_shape 5).cells := latin_dtt_base_mem 3 2 (by decide) (by decide)
  have b00 : 1 ≤ T ⟨(0, 0), m00⟩ ∧ T ⟨(0, 0), m00⟩ ≤ 5 := by
    have h := hb ⟨(0, 0), m00⟩
    simpa [latin_double_three_tail_shape_rowLen] using h
  have b01 : 1 ≤ T ⟨(0, 1), m01⟩ ∧ T ⟨(0, 1), m01⟩ ≤ 5 := by
    have h := hb ⟨(0, 1), m01⟩
    simpa [latin_double_three_tail_shape_rowLen] using h
  have b02 : 1 ≤ T ⟨(0, 2), m02⟩ ∧ T ⟨(0, 2), m02⟩ ≤ 5 := by
    have h := hb ⟨(0, 2), m02⟩
    simpa [latin_double_three_tail_shape_rowLen] using h
  have b03 : 1 ≤ T ⟨(0, 3), m03⟩ ∧ T ⟨(0, 3), m03⟩ ≤ 5 := by
    have h := hb ⟨(0, 3), m03⟩
    simpa [latin_double_three_tail_shape_rowLen] using h
  have b04 : 1 ≤ T ⟨(0, 4), m04⟩ ∧ T ⟨(0, 4), m04⟩ ≤ 5 := by
    have h := hb ⟨(0, 4), m04⟩
    simpa [latin_double_three_tail_shape_rowLen] using h
  have b10 : 1 ≤ T ⟨(1, 0), m10⟩ ∧ T ⟨(1, 0), m10⟩ ≤ 4 := by
    have h := hb ⟨(1, 0), m10⟩
    simpa [latin_double_three_tail_shape_rowLen] using h
  have b11 : 1 ≤ T ⟨(1, 1), m11⟩ ∧ T ⟨(1, 1), m11⟩ ≤ 4 := by
    have h := hb ⟨(1, 1), m11⟩
    simpa [latin_double_three_tail_shape_rowLen] using h
  have b12 : 1 ≤ T ⟨(1, 2), m12⟩ ∧ T ⟨(1, 2), m12⟩ ≤ 4 := by
    have h := hb ⟨(1, 2), m12⟩
    simpa [latin_double_three_tail_shape_rowLen] using h
  have b13 : 1 ≤ T ⟨(1, 3), m13⟩ ∧ T ⟨(1, 3), m13⟩ ≤ 4 := by
    have h := hb ⟨(1, 3), m13⟩
    simpa [latin_double_three_tail_shape_rowLen] using h
  have b20 : 1 ≤ T ⟨(2, 0), m20⟩ ∧ T ⟨(2, 0), m20⟩ ≤ 3 := by
    have h := hb ⟨(2, 0), m20⟩
    simpa [latin_double_three_tail_shape_rowLen] using h
  have b21 : 1 ≤ T ⟨(2, 1), m21⟩ ∧ T ⟨(2, 1), m21⟩ ≤ 3 := by
    have h := hb ⟨(2, 1), m21⟩
    simpa [latin_double_three_tail_shape_rowLen] using h
  have b22 : 1 ≤ T ⟨(2, 2), m22⟩ ∧ T ⟨(2, 2), m22⟩ ≤ 3 := by
    have h := hb ⟨(2, 2), m22⟩
    simpa [latin_double_three_tail_shape_rowLen] using h
  have b30 : 1 ≤ T ⟨(3, 0), m30⟩ ∧ T ⟨(3, 0), m30⟩ ≤ 3 := by
    have h := hb ⟨(3, 0), m30⟩
    simpa [latin_double_three_tail_shape_rowLen] using h
  have b31 : 1 ≤ T ⟨(3, 1), m31⟩ ∧ T ⟨(3, 1), m31⟩ ≤ 3 := by
    have h := hb ⟨(3, 1), m31⟩
    simpa [latin_double_three_tail_shape_rowLen] using h
  have b32 : 1 ≤ T ⟨(3, 2), m32⟩ ∧ T ⟨(3, 2), m32⟩ ≤ 3 := by
    have h := hb ⟨(3, 2), m32⟩
    simpa [latin_double_three_tail_shape_rowLen] using h
  have n0001 : T ⟨(0, 0), m00⟩ ≠ T ⟨(0, 1), m01⟩ := fun e => absurd (hr ⟨(0, 0), m00⟩ ⟨(0, 1), m01⟩ rfl e) (by simp)
  have n0002 : T ⟨(0, 0), m00⟩ ≠ T ⟨(0, 2), m02⟩ := fun e => absurd (hr ⟨(0, 0), m00⟩ ⟨(0, 2), m02⟩ rfl e) (by simp)
  have n0003 : T ⟨(0, 0), m00⟩ ≠ T ⟨(0, 3), m03⟩ := fun e => absurd (hr ⟨(0, 0), m00⟩ ⟨(0, 3), m03⟩ rfl e) (by simp)
  have n0004 : T ⟨(0, 0), m00⟩ ≠ T ⟨(0, 4), m04⟩ := fun e => absurd (hr ⟨(0, 0), m00⟩ ⟨(0, 4), m04⟩ rfl e) (by simp)
  have n0010 : T ⟨(0, 0), m00⟩ ≠ T ⟨(1, 0), m10⟩ := fun e => absurd (hcl ⟨(0, 0), m00⟩ ⟨(1, 0), m10⟩ rfl e) (by simp)
  have n0020 : T ⟨(0, 0), m00⟩ ≠ T ⟨(2, 0), m20⟩ := fun e => absurd (hcl ⟨(0, 0), m00⟩ ⟨(2, 0), m20⟩ rfl e) (by simp)
  have n0030 : T ⟨(0, 0), m00⟩ ≠ T ⟨(3, 0), m30⟩ := fun e => absurd (hcl ⟨(0, 0), m00⟩ ⟨(3, 0), m30⟩ rfl e) (by simp)
  have n0102 : T ⟨(0, 1), m01⟩ ≠ T ⟨(0, 2), m02⟩ := fun e => absurd (hr ⟨(0, 1), m01⟩ ⟨(0, 2), m02⟩ rfl e) (by simp)
  have n0103 : T ⟨(0, 1), m01⟩ ≠ T ⟨(0, 3), m03⟩ := fun e => absurd (hr ⟨(0, 1), m01⟩ ⟨(0, 3), m03⟩ rfl e) (by simp)
  have n0104 : T ⟨(0, 1), m01⟩ ≠ T ⟨(0, 4), m04⟩ := fun e => absurd (hr ⟨(0, 1), m01⟩ ⟨(0, 4), m04⟩ rfl e) (by simp)
  have n0111 : T ⟨(0, 1), m01⟩ ≠ T ⟨(1, 1), m11⟩ := fun e => absurd (hcl ⟨(0, 1), m01⟩ ⟨(1, 1), m11⟩ rfl e) (by simp)
  have n0121 : T ⟨(0, 1), m01⟩ ≠ T ⟨(2, 1), m21⟩ := fun e => absurd (hcl ⟨(0, 1), m01⟩ ⟨(2, 1), m21⟩ rfl e) (by simp)
  have n0131 : T ⟨(0, 1), m01⟩ ≠ T ⟨(3, 1), m31⟩ := fun e => absurd (hcl ⟨(0, 1), m01⟩ ⟨(3, 1), m31⟩ rfl e) (by simp)
  have n0203 : T ⟨(0, 2), m02⟩ ≠ T ⟨(0, 3), m03⟩ := fun e => absurd (hr ⟨(0, 2), m02⟩ ⟨(0, 3), m03⟩ rfl e) (by simp)
  have n0204 : T ⟨(0, 2), m02⟩ ≠ T ⟨(0, 4), m04⟩ := fun e => absurd (hr ⟨(0, 2), m02⟩ ⟨(0, 4), m04⟩ rfl e) (by simp)
  have n0212 : T ⟨(0, 2), m02⟩ ≠ T ⟨(1, 2), m12⟩ := fun e => absurd (hcl ⟨(0, 2), m02⟩ ⟨(1, 2), m12⟩ rfl e) (by simp)
  have n0222 : T ⟨(0, 2), m02⟩ ≠ T ⟨(2, 2), m22⟩ := fun e => absurd (hcl ⟨(0, 2), m02⟩ ⟨(2, 2), m22⟩ rfl e) (by simp)
  have n0232 : T ⟨(0, 2), m02⟩ ≠ T ⟨(3, 2), m32⟩ := fun e => absurd (hcl ⟨(0, 2), m02⟩ ⟨(3, 2), m32⟩ rfl e) (by simp)
  have n0304 : T ⟨(0, 3), m03⟩ ≠ T ⟨(0, 4), m04⟩ := fun e => absurd (hr ⟨(0, 3), m03⟩ ⟨(0, 4), m04⟩ rfl e) (by simp)
  have n0313 : T ⟨(0, 3), m03⟩ ≠ T ⟨(1, 3), m13⟩ := fun e => absurd (hcl ⟨(0, 3), m03⟩ ⟨(1, 3), m13⟩ rfl e) (by simp)
  have n1011 : T ⟨(1, 0), m10⟩ ≠ T ⟨(1, 1), m11⟩ := fun e => absurd (hr ⟨(1, 0), m10⟩ ⟨(1, 1), m11⟩ rfl e) (by simp)
  have n1012 : T ⟨(1, 0), m10⟩ ≠ T ⟨(1, 2), m12⟩ := fun e => absurd (hr ⟨(1, 0), m10⟩ ⟨(1, 2), m12⟩ rfl e) (by simp)
  have n1013 : T ⟨(1, 0), m10⟩ ≠ T ⟨(1, 3), m13⟩ := fun e => absurd (hr ⟨(1, 0), m10⟩ ⟨(1, 3), m13⟩ rfl e) (by simp)
  have n1020 : T ⟨(1, 0), m10⟩ ≠ T ⟨(2, 0), m20⟩ := fun e => absurd (hcl ⟨(1, 0), m10⟩ ⟨(2, 0), m20⟩ rfl e) (by simp)
  have n1030 : T ⟨(1, 0), m10⟩ ≠ T ⟨(3, 0), m30⟩ := fun e => absurd (hcl ⟨(1, 0), m10⟩ ⟨(3, 0), m30⟩ rfl e) (by simp)
  have n1112 : T ⟨(1, 1), m11⟩ ≠ T ⟨(1, 2), m12⟩ := fun e => absurd (hr ⟨(1, 1), m11⟩ ⟨(1, 2), m12⟩ rfl e) (by simp)
  have n1113 : T ⟨(1, 1), m11⟩ ≠ T ⟨(1, 3), m13⟩ := fun e => absurd (hr ⟨(1, 1), m11⟩ ⟨(1, 3), m13⟩ rfl e) (by simp)
  have n1121 : T ⟨(1, 1), m11⟩ ≠ T ⟨(2, 1), m21⟩ := fun e => absurd (hcl ⟨(1, 1), m11⟩ ⟨(2, 1), m21⟩ rfl e) (by simp)
  have n1131 : T ⟨(1, 1), m11⟩ ≠ T ⟨(3, 1), m31⟩ := fun e => absurd (hcl ⟨(1, 1), m11⟩ ⟨(3, 1), m31⟩ rfl e) (by simp)
  have n1213 : T ⟨(1, 2), m12⟩ ≠ T ⟨(1, 3), m13⟩ := fun e => absurd (hr ⟨(1, 2), m12⟩ ⟨(1, 3), m13⟩ rfl e) (by simp)
  have n1222 : T ⟨(1, 2), m12⟩ ≠ T ⟨(2, 2), m22⟩ := fun e => absurd (hcl ⟨(1, 2), m12⟩ ⟨(2, 2), m22⟩ rfl e) (by simp)
  have n1232 : T ⟨(1, 2), m12⟩ ≠ T ⟨(3, 2), m32⟩ := fun e => absurd (hcl ⟨(1, 2), m12⟩ ⟨(3, 2), m32⟩ rfl e) (by simp)
  have n2021 : T ⟨(2, 0), m20⟩ ≠ T ⟨(2, 1), m21⟩ := fun e => absurd (hr ⟨(2, 0), m20⟩ ⟨(2, 1), m21⟩ rfl e) (by simp)
  have n2022 : T ⟨(2, 0), m20⟩ ≠ T ⟨(2, 2), m22⟩ := fun e => absurd (hr ⟨(2, 0), m20⟩ ⟨(2, 2), m22⟩ rfl e) (by simp)
  have n2030 : T ⟨(2, 0), m20⟩ ≠ T ⟨(3, 0), m30⟩ := fun e => absurd (hcl ⟨(2, 0), m20⟩ ⟨(3, 0), m30⟩ rfl e) (by simp)
  have n2122 : T ⟨(2, 1), m21⟩ ≠ T ⟨(2, 2), m22⟩ := fun e => absurd (hr ⟨(2, 1), m21⟩ ⟨(2, 2), m22⟩ rfl e) (by simp)
  have n2131 : T ⟨(2, 1), m21⟩ ≠ T ⟨(3, 1), m31⟩ := fun e => absurd (hcl ⟨(2, 1), m21⟩ ⟨(3, 1), m31⟩ rfl e) (by simp)
  have n2232 : T ⟨(2, 2), m22⟩ ≠ T ⟨(3, 2), m32⟩ := fun e => absurd (hcl ⟨(2, 2), m22⟩ ⟨(3, 2), m32⟩ rfl e) (by simp)
  have n3031 : T ⟨(3, 0), m30⟩ ≠ T ⟨(3, 1), m31⟩ := fun e => absurd (hr ⟨(3, 0), m30⟩ ⟨(3, 1), m31⟩ rfl e) (by simp)
  have n3032 : T ⟨(3, 0), m30⟩ ≠ T ⟨(3, 2), m32⟩ := fun e => absurd (hr ⟨(3, 0), m30⟩ ⟨(3, 2), m32⟩ rfl e) (by simp)
  have n3132 : T ⟨(3, 1), m31⟩ ≠ T ⟨(3, 2), m32⟩ := fun e => absurd (hr ⟨(3, 1), m31⟩ ⟨(3, 2), m32⟩ rfl e) (by simp)
  have e00 : latin_dtt_base_g T 0 0 = T ⟨(0, 0), m00⟩ := dif_pos m00
  have e01 : latin_dtt_base_g T 0 1 = T ⟨(0, 1), m01⟩ := dif_pos m01
  have e02 : latin_dtt_base_g T 0 2 = T ⟨(0, 2), m02⟩ := dif_pos m02
  have e03 : latin_dtt_base_g T 0 3 = T ⟨(0, 3), m03⟩ := dif_pos m03
  have e04 : latin_dtt_base_g T 0 4 = T ⟨(0, 4), m04⟩ := dif_pos m04
  have e10 : latin_dtt_base_g T 1 0 = T ⟨(1, 0), m10⟩ := dif_pos m10
  have e11 : latin_dtt_base_g T 1 1 = T ⟨(1, 1), m11⟩ := dif_pos m11
  have e12 : latin_dtt_base_g T 1 2 = T ⟨(1, 2), m12⟩ := dif_pos m12
  have e13 : latin_dtt_base_g T 1 3 = T ⟨(1, 3), m13⟩ := dif_pos m13
  have e20 : latin_dtt_base_g T 2 0 = T ⟨(2, 0), m20⟩ := dif_pos m20
  have e21 : latin_dtt_base_g T 2 1 = T ⟨(2, 1), m21⟩ := dif_pos m21
  have e22 : latin_dtt_base_g T 2 2 = T ⟨(2, 2), m22⟩ := dif_pos m22
  have e30 : latin_dtt_base_g T 3 0 = T ⟨(3, 0), m30⟩ := dif_pos m30
  have e31 : latin_dtt_base_g T 3 1 = T ⟨(3, 1), m31⟩ := dif_pos m31
  have e32 : latin_dtt_base_g T 3 2 = T ⟨(3, 2), m32⟩ := dif_pos m32
  have hF : latin_dtt_base_F T = ([latin_dtt_base_g T 0 0, latin_dtt_base_g T 0 1, latin_dtt_base_g T 0 2, latin_dtt_base_g T 0 3, latin_dtt_base_g T 0 4], [latin_dtt_base_g T 1 0, latin_dtt_base_g T 1 1, latin_dtt_base_g T 1 2, latin_dtt_base_g T 1 3], [latin_dtt_base_g T 2 0, latin_dtt_base_g T 2 1, latin_dtt_base_g T 2 2], [latin_dtt_base_g T 3 0, latin_dtt_base_g T 3 1, latin_dtt_base_g T 3 2]) := rfl
  rw [hF, e00, e01, e02, e03, e04, e10, e11, e12, e13, e20, e21, e22, e30, e31, e32]
  exact latin_dtt_base_fwd (T ⟨(0, 0), m00⟩) (T ⟨(0, 1), m01⟩) (T ⟨(0, 2), m02⟩) (T ⟨(0, 3), m03⟩) (T ⟨(0, 4), m04⟩) (T ⟨(1, 0), m10⟩) (T ⟨(1, 1), m11⟩) (T ⟨(1, 2), m12⟩) (T ⟨(1, 3), m13⟩) (T ⟨(2, 0), m20⟩) (T ⟨(2, 1), m21⟩) (T ⟨(2, 2), m22⟩) (T ⟨(3, 0), m30⟩) (T ⟨(3, 1), m31⟩) (T ⟨(3, 2), m32⟩) b00 b01 b02 b03 b04 b10 b11 b12 b13 b20 b21 b22 b30 b31 b32 n0001 n0002 n0003 n0004 n0010 n0020 n0030 n0102 n0103 n0104 n0111 n0121 n0131 n0203 n0204 n0212 n0222 n0232 n0304 n0313 n1011 n1012 n1013 n1020 n1030 n1112 n1113 n1121 n1131 n1213 n1222 n1232 n2021 n2022 n2030 n2122 n2131 n2232 n3031 n3032 n3132

theorem latin_dtt_base_F_inj : Set.InjOn latin_dtt_base_F (latin_tableaux (latin_double_three_tail_shape 5) : Set ((latin_double_three_tail_shape 5).cells → ℕ)) := by
  intro T1 _ T2 _ hF
  funext c
  obtain ⟨hi, hj⟩ := latin_dtt_base_cell c
  have key : ∀ i, i < 4 → ∀ j, j < latin_dtt_base_len i → latin_dtt_base_g T1 i j = latin_dtt_base_g T2 i j := by
    intro i hi j hj
    have h0 := congrArg (fun x => (latin_dtt_base_row x i).getD j 0) hF
    simp only [latin_dtt_base_F] at h0
    interval_cases i <;> simp only [latin_dtt_base_row, latin_dtt_base_len] at h0 hj <;> norm_num at hj <;>
      rwa [latin_dtt_base_getD_map_range _ _ _ hj, latin_dtt_base_getD_map_range _ _ _ hj] at h0
  have := key _ hi _ hj
  simpa [latin_dtt_base_g, c.2] using this


theorem latin_dtt_base_chk_spec (x : List ℕ × List ℕ × List ℕ × List ℕ) (h : latin_dtt_base_chk x = true) :
    (∀ i < 4, (latin_dtt_base_row x i).length = latin_dtt_base_len i) ∧
    (∀ i < 4, ∀ j < latin_dtt_base_len i, 1 ≤ (latin_dtt_base_row x i).getD j 0 ∧ (latin_dtt_base_row x i).getD j 0 ≤ latin_dtt_base_len i) ∧
    (∀ i < 4, ∀ j < latin_dtt_base_len i, ∀ j' < latin_dtt_base_len i,
      (latin_dtt_base_row x i).getD j 0 = (latin_dtt_base_row x i).getD j' 0 → j = j') ∧
    (∀ i < 4, ∀ j < latin_dtt_base_len i, ∀ i' < 4, j < latin_dtt_base_len i' →
      (latin_dtt_base_row x i).getD j 0 = (latin_dtt_base_row x i').getD j 0 → i = i') := by
  simp only [latin_dtt_base_chk, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at h
  refine ⟨fun i hi => (h i hi).1, fun i hi j hj => ?_, fun i hi j hj j' hj' e => ?_,
    fun i hi j hj i' hi' hj2 e => ?_⟩
  · have := (h i hi).2 j hj
    exact ⟨this.1.1.1, this.1.1.2⟩
  · have := (h i hi).2 j hj
    rcases this.1.2 j' hj' with h1 | h1
    · exact absurd e h1
    · exact h1
  · have := (h i hi).2 j hj
    rcases this.2 i' hi' with (h1 | h1) | h1
    · simp at h1; omega
    · exact absurd e h1
    · exact h1

theorem latin_dtt_base_T_mem (x : List ℕ × List ℕ × List ℕ × List ℕ) (hx : latin_dtt_base_chk x = true) :
    (fun c : (latin_double_three_tail_shape 5).cells => (latin_dtt_base_row x c.1.1).getD c.1.2 0) ∈
      latin_tableaux (latin_double_three_tail_shape 5) := by
  obtain ⟨-, hb, hrow, hcol⟩ := latin_dtt_base_chk_spec x hx
  simp only [latin_tableaux, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc]
  refine ⟨fun c => ?_, fun c1 c2 h1 h2 => ?_, fun c1 c2 h1 h2 => ?_⟩
  · obtain ⟨hi, hj⟩ := latin_dtt_base_cell c
    rw [latin_double_three_tail_shape_rowLen]
    exact hb _ hi _ hj
  · obtain ⟨hi1, hj1⟩ := latin_dtt_base_cell c1
    obtain ⟨hi2, hj2⟩ := latin_dtt_base_cell c2
    rw [h1] at h2 hj1
    exact hrow _ hi2 _ hj1 _ hj2 h2
  · obtain ⟨hi1, hj1⟩ := latin_dtt_base_cell c1
    obtain ⟨hi2, hj2⟩ := latin_dtt_base_cell c2
    rw [← h1] at h2 hj2
    exact hcol _ hi1 _ hj1 _ hi2 hj2 h2

theorem latin_dtt_base_F_T (x : List ℕ × List ℕ × List ℕ × List ℕ) (hx : latin_dtt_base_chk x = true) :
    latin_dtt_base_F (fun c : (latin_double_three_tail_shape 5).cells => (latin_dtt_base_row x c.1.1).getD c.1.2 0) = x := by
  obtain ⟨hl, -, -, -⟩ := latin_dtt_base_chk_spec x hx
  have key : ∀ i, i < 4 → (List.range (latin_dtt_base_len i)).map
      (latin_dtt_base_g (fun c : (latin_double_three_tail_shape 5).cells => (latin_dtt_base_row x c.1.1).getD c.1.2 0) i) =
        latin_dtt_base_row x i := by
    intro i hi
    apply List.ext_getElem
    · simp [hl i hi]
    · intro j h1 h2
      simp only [List.getElem_map, List.getElem_range]
      have hj : j < latin_dtt_base_len i := by simpa using h1
      rw [latin_dtt_base_g, dif_pos (latin_dtt_base_mem i j hi hj)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
  show ((List.range (latin_dtt_base_len 0)).map _, (List.range (latin_dtt_base_len 1)).map _, (List.range (latin_dtt_base_len 2)).map _,
    (List.range (latin_dtt_base_len 3)).map _) = x
  rw [key 0 (by decide), key 1 (by decide), key 2 (by decide), key 3 (by decide)]
  rfl

theorem latin_double_three_tail_count_base : latin_tableaux_count (latin_double_three_tail_shape 5) = 144 := by
  unfold latin_tableaux_count
  have himg : (latin_tableaux (latin_double_three_tail_shape 5)).image latin_dtt_base_F = latin_dtt_base_gen.toFinset := by
    ext x
    simp only [Finset.mem_image, List.mem_toFinset]
    constructor
    · rintro ⟨T, hT, rfl⟩
      exact latin_dtt_base_F_mem T hT
    · intro hx
      exact ⟨_, latin_dtt_base_T_mem x (latin_dtt_base_gen_chk x hx), latin_dtt_base_F_T x (latin_dtt_base_gen_chk x hx)⟩
  rw [← Finset.card_image_of_injOn latin_dtt_base_F_inj, himg, List.toFinset_card_of_nodup latin_dtt_base_gen_nodup,
    latin_dtt_base_gen_length]
