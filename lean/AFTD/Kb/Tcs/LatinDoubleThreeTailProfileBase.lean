import AFTD.Prelude
import AFTD.Kb.Tcs.LatinDoubleThreeTailShape
import AFTD.Kb.Tcs.LatinTableaux
import AFTD.Kb.Tcs.LatinDoubleThreeTailProfile
import AFTD.Kb.Tcs.LatinTableauxShape5TailCols
import AFTD.Kb.Tcs.LatinColumnSymbols
import AFTD.Kb.Tcs.LatinDoubleThreeTailShapeRowLen
import AFTD.Kb.Tcs.MemLatinDoubleThreeTailShape
import AFTD.Kb.Tcs.MemLatinColumnSymbols

/-!
# latin_double_three_tail_profile_base

Topic: combinatorics   Node: 0356c02b046e

Provenance: helper lemma. Helper for the open enumeration problem in https://arxiv.org/html/2610.29291v1, Conjecture 6.3, using the availability-permanent identity of Lemma 5.4. Exact computational route: experiments 4100, 4103 and 4106.

Every Latin tableau of shape (5,4,3,3) has the specified column profile.
-/

theorem latin_double_three_tail_profile_base_set4 (x y z w : ℕ) (hx : 1 ≤ x ∧ x ≤ 4) (hy : 1 ≤ y ∧ y ≤ 4) (hz : 1 ≤ z ∧ z ≤ 4)
    (hw : 1 ≤ w ∧ w ≤ 4) (h1 : x ≠ y) (h2 : x ≠ z) (h3 : x ≠ w) (h4 : y ≠ z) (h5 : y ≠ w)
    (h6 : z ≠ w) : ({x, y, z, w} : Finset ℕ) = Finset.Icc 1 (5 - 1) := by
  ext v
  simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_Icc]
  omega

theorem latin_double_three_tail_profile_base_set5 (x y z w : ℕ) (hx : 1 ≤ x ∧ x ≤ 5) (hy : 1 ≤ y ∧ y ≤ 4) (hz : 1 ≤ z ∧ z ≤ 3)
    (hw : 1 ≤ w ∧ w ≤ 3) (hx4 : x ≠ 4) (hy4 : y ≠ 4) (h1 : x ≠ y) (h2 : x ≠ z) (h3 : x ≠ w)
    (h4 : y ≠ z) (h5 : y ≠ w) (h6 : z ≠ w) :
    ({x, y, z, w} : Finset ℕ) = Finset.Icc 1 (5 - 2) ∪ {5} := by
  ext v
  simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_Icc, Finset.mem_union]
  omega

theorem latin_double_three_tail_profile_base_no3 (x y z w : ℕ) (hx : 1 ≤ x ∧ x ≤ 3) (hy : 1 ≤ y ∧ y ≤ 3) (hz : 1 ≤ z ∧ z ≤ 3)
    (hw : 1 ≤ w ∧ w ≤ 3) (h1 : x ≠ y) (h2 : x ≠ z) (h3 : x ≠ w) (h4 : y ≠ z) (h5 : y ≠ w)
    (h6 : z ≠ w) : False := by
  omega

theorem latin_double_three_tail_profile_base_five (a0 a1 a2 a3 a4 : ℕ) (h0 : 1 ≤ a0 ∧ a0 ≤ 5) (h1 : 1 ≤ a1 ∧ a1 ≤ 5)
    (h2 : 1 ≤ a2 ∧ a2 ≤ 5) (h3 : 1 ≤ a3 ∧ a3 ≤ 3) (h4 : 1 ≤ a4 ∧ a4 ≤ 3)
    (d01 : a0 ≠ a1) (d02 : a0 ≠ a2) (d03 : a0 ≠ a3) (d04 : a0 ≠ a4) (d12 : a1 ≠ a2)
    (d13 : a1 ≠ a3) (d14 : a1 ≠ a4) (d23 : a2 ≠ a3) (d24 : a2 ≠ a4) (d34 : a3 ≠ a4) :
    (a0 = 5 ∨ a1 = 5 ∨ a2 = 5) ∧ (a0 = 4 ∨ a1 = 4 ∨ a2 = 4) := by
  omega

theorem latin_double_three_tail_profile_base_four (b0 b1 b2 b3 : ℕ) (h0 : 1 ≤ b0 ∧ b0 ≤ 4) (h1 : 1 ≤ b1 ∧ b1 ≤ 4)
    (h2 : 1 ≤ b2 ∧ b2 ≤ 4) (h3 : 1 ≤ b3 ∧ b3 ≤ 3)
    (d01 : b0 ≠ b1) (d02 : b0 ≠ b2) (d03 : b0 ≠ b3) (d12 : b1 ≠ b2) (d13 : b1 ≠ b3)
    (d23 : b2 ≠ b3) : b0 = 4 ∨ b1 = 4 ∨ b2 = 4 := by
  omega

theorem latin_double_three_tail_profile_base_le4 (x y : ℕ) (hx : x ≤ 5) (hy : y = 5) (h : x ≠ y) : x ≤ 4 := by omega

theorem latin_double_three_tail_profile_base_le3a (x y z : ℕ) (hx : x ≤ 5) (hy : y = 5) (hz : z = 4) (h1 : x ≠ y) (h2 : x ≠ z) :
    x ≤ 3 := by omega

theorem latin_double_three_tail_profile_base_le3b (x y : ℕ) (hx : x ≤ 4) (hy : y = 4) (h : x ≠ y) : x ≤ 3 := by omega

theorem latin_double_three_tail_profile_base_col (T : (latin_double_three_tail_shape 5).cells → ℕ) (j : ℕ) (hj : j < 3) :
    latin_column_symbols (latin_double_three_tail_shape 5) T j =
      {T ⟨(0, j), (mem_latin_double_three_tail_shape 5 0 j).mpr ⟨by omega, by simp; omega⟩⟩,
       T ⟨(1, j), (mem_latin_double_three_tail_shape 5 1 j).mpr ⟨by omega, by simp; omega⟩⟩,
       T ⟨(2, j), (mem_latin_double_three_tail_shape 5 2 j).mpr ⟨by omega, by simp; omega⟩⟩,
       T ⟨(3, j), (mem_latin_double_three_tail_shape 5 3 j).mpr ⟨by omega, by simp; omega⟩⟩} := by
  ext x
  rw [mem_latin_column_symbols]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨⟨i, j'⟩, hc⟩, hj', hx⟩
    simp only at hj'
    subst hj'
    have hi := ((mem_latin_double_three_tail_shape 5 i _).mp hc).1
    interval_cases i
    · left; exact hx.symm
    · right; left; exact hx.symm
    · right; right; left; exact hx.symm
    · right; right; right; exact hx.symm
  · rintro (h | h | h | h) <;> exact ⟨⟨_, _⟩, rfl, h.symm⟩

theorem latin_double_three_tail_profile_base : ∀ T ∈ latin_tableaux (latin_double_three_tail_shape 5), latin_double_three_tail_profile 5 T := by
  intro T hT
  obtain ⟨s, hs, h4, h3⟩ := latin_tableaux_shape5_tail_cols T hT
  have hT' := hT
  simp only [latin_tableaux, Finset.mem_filter, Fintype.mem_piFinset] at hT'
  obtain ⟨hb, hr, hcl⟩ := hT'
  have rl : ∀ i, (latin_double_three_tail_shape 5).rowLen i = if i < 4 then max 3 (5 - i) else 0 :=
    fun i => latin_double_three_tail_shape_rowLen 5 i
  have m00 : (0, 0) ∈ (latin_double_three_tail_shape 5).cells :=
    (mem_latin_double_three_tail_shape 5 0 0).mpr ⟨by omega, by simp⟩
  have b00 : 1 ≤ T ⟨(0, 0), m00⟩ ∧ T ⟨(0, 0), m00⟩ ≤ 5 := by
    have h := hb ⟨(0, 0), m00⟩
    simp only [rl, Finset.mem_Icc] at h
    norm_num at h
    exact h
  have m01 : (0, 1) ∈ (latin_double_three_tail_shape 5).cells :=
    (mem_latin_double_three_tail_shape 5 0 1).mpr ⟨by omega, by simp⟩
  have b01 : 1 ≤ T ⟨(0, 1), m01⟩ ∧ T ⟨(0, 1), m01⟩ ≤ 5 := by
    have h := hb ⟨(0, 1), m01⟩
    simp only [rl, Finset.mem_Icc] at h
    norm_num at h
    exact h
  have m02 : (0, 2) ∈ (latin_double_three_tail_shape 5).cells :=
    (mem_latin_double_three_tail_shape 5 0 2).mpr ⟨by omega, by simp⟩
  have b02 : 1 ≤ T ⟨(0, 2), m02⟩ ∧ T ⟨(0, 2), m02⟩ ≤ 5 := by
    have h := hb ⟨(0, 2), m02⟩
    simp only [rl, Finset.mem_Icc] at h
    norm_num at h
    exact h
  have m03 : (0, 3) ∈ (latin_double_three_tail_shape 5).cells :=
    (mem_latin_double_three_tail_shape 5 0 3).mpr ⟨by omega, by simp⟩
  have b03 : 1 ≤ T ⟨(0, 3), m03⟩ ∧ T ⟨(0, 3), m03⟩ ≤ 5 := by
    have h := hb ⟨(0, 3), m03⟩
    simp only [rl, Finset.mem_Icc] at h
    norm_num at h
    exact h
  have m04 : (0, 4) ∈ (latin_double_three_tail_shape 5).cells :=
    (mem_latin_double_three_tail_shape 5 0 4).mpr ⟨by omega, by simp⟩
  have b04 : 1 ≤ T ⟨(0, 4), m04⟩ ∧ T ⟨(0, 4), m04⟩ ≤ 5 := by
    have h := hb ⟨(0, 4), m04⟩
    simp only [rl, Finset.mem_Icc] at h
    norm_num at h
    exact h
  have m10 : (1, 0) ∈ (latin_double_three_tail_shape 5).cells :=
    (mem_latin_double_three_tail_shape 5 1 0).mpr ⟨by omega, by simp⟩
  have b10 : 1 ≤ T ⟨(1, 0), m10⟩ ∧ T ⟨(1, 0), m10⟩ ≤ 4 := by
    have h := hb ⟨(1, 0), m10⟩
    simp only [rl, Finset.mem_Icc] at h
    norm_num at h
    exact h
  have m11 : (1, 1) ∈ (latin_double_three_tail_shape 5).cells :=
    (mem_latin_double_three_tail_shape 5 1 1).mpr ⟨by omega, by simp⟩
  have b11 : 1 ≤ T ⟨(1, 1), m11⟩ ∧ T ⟨(1, 1), m11⟩ ≤ 4 := by
    have h := hb ⟨(1, 1), m11⟩
    simp only [rl, Finset.mem_Icc] at h
    norm_num at h
    exact h
  have m12 : (1, 2) ∈ (latin_double_three_tail_shape 5).cells :=
    (mem_latin_double_three_tail_shape 5 1 2).mpr ⟨by omega, by simp⟩
  have b12 : 1 ≤ T ⟨(1, 2), m12⟩ ∧ T ⟨(1, 2), m12⟩ ≤ 4 := by
    have h := hb ⟨(1, 2), m12⟩
    simp only [rl, Finset.mem_Icc] at h
    norm_num at h
    exact h
  have m13 : (1, 3) ∈ (latin_double_three_tail_shape 5).cells :=
    (mem_latin_double_three_tail_shape 5 1 3).mpr ⟨by omega, by simp⟩
  have b13 : 1 ≤ T ⟨(1, 3), m13⟩ ∧ T ⟨(1, 3), m13⟩ ≤ 4 := by
    have h := hb ⟨(1, 3), m13⟩
    simp only [rl, Finset.mem_Icc] at h
    norm_num at h
    exact h
  have m20 : (2, 0) ∈ (latin_double_three_tail_shape 5).cells :=
    (mem_latin_double_three_tail_shape 5 2 0).mpr ⟨by omega, by simp⟩
  have b20 : 1 ≤ T ⟨(2, 0), m20⟩ ∧ T ⟨(2, 0), m20⟩ ≤ 3 := by
    have h := hb ⟨(2, 0), m20⟩
    simp only [rl, Finset.mem_Icc] at h
    norm_num at h
    exact h
  have m21 : (2, 1) ∈ (latin_double_three_tail_shape 5).cells :=
    (mem_latin_double_three_tail_shape 5 2 1).mpr ⟨by omega, by simp⟩
  have b21 : 1 ≤ T ⟨(2, 1), m21⟩ ∧ T ⟨(2, 1), m21⟩ ≤ 3 := by
    have h := hb ⟨(2, 1), m21⟩
    simp only [rl, Finset.mem_Icc] at h
    norm_num at h
    exact h
  have m22 : (2, 2) ∈ (latin_double_three_tail_shape 5).cells :=
    (mem_latin_double_three_tail_shape 5 2 2).mpr ⟨by omega, by simp⟩
  have b22 : 1 ≤ T ⟨(2, 2), m22⟩ ∧ T ⟨(2, 2), m22⟩ ≤ 3 := by
    have h := hb ⟨(2, 2), m22⟩
    simp only [rl, Finset.mem_Icc] at h
    norm_num at h
    exact h
  have m30 : (3, 0) ∈ (latin_double_three_tail_shape 5).cells :=
    (mem_latin_double_three_tail_shape 5 3 0).mpr ⟨by omega, by simp⟩
  have b30 : 1 ≤ T ⟨(3, 0), m30⟩ ∧ T ⟨(3, 0), m30⟩ ≤ 3 := by
    have h := hb ⟨(3, 0), m30⟩
    simp only [rl, Finset.mem_Icc] at h
    norm_num at h
    exact h
  have m31 : (3, 1) ∈ (latin_double_three_tail_shape 5).cells :=
    (mem_latin_double_three_tail_shape 5 3 1).mpr ⟨by omega, by simp⟩
  have b31 : 1 ≤ T ⟨(3, 1), m31⟩ ∧ T ⟨(3, 1), m31⟩ ≤ 3 := by
    have h := hb ⟨(3, 1), m31⟩
    simp only [rl, Finset.mem_Icc] at h
    norm_num at h
    exact h
  have m32 : (3, 2) ∈ (latin_double_three_tail_shape 5).cells :=
    (mem_latin_double_three_tail_shape 5 3 2).mpr ⟨by omega, by simp⟩
  have b32 : 1 ≤ T ⟨(3, 2), m32⟩ ∧ T ⟨(3, 2), m32⟩ ≤ 3 := by
    have h := hb ⟨(3, 2), m32⟩
    simp only [rl, Finset.mem_Icc] at h
    norm_num at h
    exact h
  have n00_01 : T ⟨(0, 0), m00⟩ ≠ T ⟨(0, 1), m01⟩ := fun h => by
    have := hr ⟨(0, 0), m00⟩ ⟨(0, 1), m01⟩ rfl h
    simp at this
  have n00_02 : T ⟨(0, 0), m00⟩ ≠ T ⟨(0, 2), m02⟩ := fun h => by
    have := hr ⟨(0, 0), m00⟩ ⟨(0, 2), m02⟩ rfl h
    simp at this
  have n00_03 : T ⟨(0, 0), m00⟩ ≠ T ⟨(0, 3), m03⟩ := fun h => by
    have := hr ⟨(0, 0), m00⟩ ⟨(0, 3), m03⟩ rfl h
    simp at this
  have n00_04 : T ⟨(0, 0), m00⟩ ≠ T ⟨(0, 4), m04⟩ := fun h => by
    have := hr ⟨(0, 0), m00⟩ ⟨(0, 4), m04⟩ rfl h
    simp at this
  have n00_10 : T ⟨(0, 0), m00⟩ ≠ T ⟨(1, 0), m10⟩ := fun h => by
    have := hcl ⟨(0, 0), m00⟩ ⟨(1, 0), m10⟩ rfl h
    simp at this
  have n00_20 : T ⟨(0, 0), m00⟩ ≠ T ⟨(2, 0), m20⟩ := fun h => by
    have := hcl ⟨(0, 0), m00⟩ ⟨(2, 0), m20⟩ rfl h
    simp at this
  have n00_30 : T ⟨(0, 0), m00⟩ ≠ T ⟨(3, 0), m30⟩ := fun h => by
    have := hcl ⟨(0, 0), m00⟩ ⟨(3, 0), m30⟩ rfl h
    simp at this
  have n01_02 : T ⟨(0, 1), m01⟩ ≠ T ⟨(0, 2), m02⟩ := fun h => by
    have := hr ⟨(0, 1), m01⟩ ⟨(0, 2), m02⟩ rfl h
    simp at this
  have n01_03 : T ⟨(0, 1), m01⟩ ≠ T ⟨(0, 3), m03⟩ := fun h => by
    have := hr ⟨(0, 1), m01⟩ ⟨(0, 3), m03⟩ rfl h
    simp at this
  have n01_04 : T ⟨(0, 1), m01⟩ ≠ T ⟨(0, 4), m04⟩ := fun h => by
    have := hr ⟨(0, 1), m01⟩ ⟨(0, 4), m04⟩ rfl h
    simp at this
  have n01_11 : T ⟨(0, 1), m01⟩ ≠ T ⟨(1, 1), m11⟩ := fun h => by
    have := hcl ⟨(0, 1), m01⟩ ⟨(1, 1), m11⟩ rfl h
    simp at this
  have n01_21 : T ⟨(0, 1), m01⟩ ≠ T ⟨(2, 1), m21⟩ := fun h => by
    have := hcl ⟨(0, 1), m01⟩ ⟨(2, 1), m21⟩ rfl h
    simp at this
  have n01_31 : T ⟨(0, 1), m01⟩ ≠ T ⟨(3, 1), m31⟩ := fun h => by
    have := hcl ⟨(0, 1), m01⟩ ⟨(3, 1), m31⟩ rfl h
    simp at this
  have n02_03 : T ⟨(0, 2), m02⟩ ≠ T ⟨(0, 3), m03⟩ := fun h => by
    have := hr ⟨(0, 2), m02⟩ ⟨(0, 3), m03⟩ rfl h
    simp at this
  have n02_04 : T ⟨(0, 2), m02⟩ ≠ T ⟨(0, 4), m04⟩ := fun h => by
    have := hr ⟨(0, 2), m02⟩ ⟨(0, 4), m04⟩ rfl h
    simp at this
  have n02_12 : T ⟨(0, 2), m02⟩ ≠ T ⟨(1, 2), m12⟩ := fun h => by
    have := hcl ⟨(0, 2), m02⟩ ⟨(1, 2), m12⟩ rfl h
    simp at this
  have n02_22 : T ⟨(0, 2), m02⟩ ≠ T ⟨(2, 2), m22⟩ := fun h => by
    have := hcl ⟨(0, 2), m02⟩ ⟨(2, 2), m22⟩ rfl h
    simp at this
  have n02_32 : T ⟨(0, 2), m02⟩ ≠ T ⟨(3, 2), m32⟩ := fun h => by
    have := hcl ⟨(0, 2), m02⟩ ⟨(3, 2), m32⟩ rfl h
    simp at this
  have n03_04 : T ⟨(0, 3), m03⟩ ≠ T ⟨(0, 4), m04⟩ := fun h => by
    have := hr ⟨(0, 3), m03⟩ ⟨(0, 4), m04⟩ rfl h
    simp at this
  have n03_13 : T ⟨(0, 3), m03⟩ ≠ T ⟨(1, 3), m13⟩ := fun h => by
    have := hcl ⟨(0, 3), m03⟩ ⟨(1, 3), m13⟩ rfl h
    simp at this
  have n10_11 : T ⟨(1, 0), m10⟩ ≠ T ⟨(1, 1), m11⟩ := fun h => by
    have := hr ⟨(1, 0), m10⟩ ⟨(1, 1), m11⟩ rfl h
    simp at this
  have n10_12 : T ⟨(1, 0), m10⟩ ≠ T ⟨(1, 2), m12⟩ := fun h => by
    have := hr ⟨(1, 0), m10⟩ ⟨(1, 2), m12⟩ rfl h
    simp at this
  have n10_13 : T ⟨(1, 0), m10⟩ ≠ T ⟨(1, 3), m13⟩ := fun h => by
    have := hr ⟨(1, 0), m10⟩ ⟨(1, 3), m13⟩ rfl h
    simp at this
  have n10_20 : T ⟨(1, 0), m10⟩ ≠ T ⟨(2, 0), m20⟩ := fun h => by
    have := hcl ⟨(1, 0), m10⟩ ⟨(2, 0), m20⟩ rfl h
    simp at this
  have n10_30 : T ⟨(1, 0), m10⟩ ≠ T ⟨(3, 0), m30⟩ := fun h => by
    have := hcl ⟨(1, 0), m10⟩ ⟨(3, 0), m30⟩ rfl h
    simp at this
  have n11_12 : T ⟨(1, 1), m11⟩ ≠ T ⟨(1, 2), m12⟩ := fun h => by
    have := hr ⟨(1, 1), m11⟩ ⟨(1, 2), m12⟩ rfl h
    simp at this
  have n11_13 : T ⟨(1, 1), m11⟩ ≠ T ⟨(1, 3), m13⟩ := fun h => by
    have := hr ⟨(1, 1), m11⟩ ⟨(1, 3), m13⟩ rfl h
    simp at this
  have n11_21 : T ⟨(1, 1), m11⟩ ≠ T ⟨(2, 1), m21⟩ := fun h => by
    have := hcl ⟨(1, 1), m11⟩ ⟨(2, 1), m21⟩ rfl h
    simp at this
  have n11_31 : T ⟨(1, 1), m11⟩ ≠ T ⟨(3, 1), m31⟩ := fun h => by
    have := hcl ⟨(1, 1), m11⟩ ⟨(3, 1), m31⟩ rfl h
    simp at this
  have n12_13 : T ⟨(1, 2), m12⟩ ≠ T ⟨(1, 3), m13⟩ := fun h => by
    have := hr ⟨(1, 2), m12⟩ ⟨(1, 3), m13⟩ rfl h
    simp at this
  have n12_22 : T ⟨(1, 2), m12⟩ ≠ T ⟨(2, 2), m22⟩ := fun h => by
    have := hcl ⟨(1, 2), m12⟩ ⟨(2, 2), m22⟩ rfl h
    simp at this
  have n12_32 : T ⟨(1, 2), m12⟩ ≠ T ⟨(3, 2), m32⟩ := fun h => by
    have := hcl ⟨(1, 2), m12⟩ ⟨(3, 2), m32⟩ rfl h
    simp at this
  have n20_21 : T ⟨(2, 0), m20⟩ ≠ T ⟨(2, 1), m21⟩ := fun h => by
    have := hr ⟨(2, 0), m20⟩ ⟨(2, 1), m21⟩ rfl h
    simp at this
  have n20_22 : T ⟨(2, 0), m20⟩ ≠ T ⟨(2, 2), m22⟩ := fun h => by
    have := hr ⟨(2, 0), m20⟩ ⟨(2, 2), m22⟩ rfl h
    simp at this
  have n20_30 : T ⟨(2, 0), m20⟩ ≠ T ⟨(3, 0), m30⟩ := fun h => by
    have := hcl ⟨(2, 0), m20⟩ ⟨(3, 0), m30⟩ rfl h
    simp at this
  have n21_22 : T ⟨(2, 1), m21⟩ ≠ T ⟨(2, 2), m22⟩ := fun h => by
    have := hr ⟨(2, 1), m21⟩ ⟨(2, 2), m22⟩ rfl h
    simp at this
  have n21_31 : T ⟨(2, 1), m21⟩ ≠ T ⟨(3, 1), m31⟩ := fun h => by
    have := hcl ⟨(2, 1), m21⟩ ⟨(3, 1), m31⟩ rfl h
    simp at this
  have n22_32 : T ⟨(2, 2), m22⟩ ≠ T ⟨(3, 2), m32⟩ := fun h => by
    have := hcl ⟨(2, 2), m22⟩ ⟨(3, 2), m32⟩ rfl h
    simp at this
  have n30_31 : T ⟨(3, 0), m30⟩ ≠ T ⟨(3, 1), m31⟩ := fun h => by
    have := hr ⟨(3, 0), m30⟩ ⟨(3, 1), m31⟩ rfl h
    simp at this
  have n30_32 : T ⟨(3, 0), m30⟩ ≠ T ⟨(3, 2), m32⟩ := fun h => by
    have := hr ⟨(3, 0), m30⟩ ⟨(3, 2), m32⟩ rfl h
    simp at this
  have n31_32 : T ⟨(3, 1), m31⟩ ≠ T ⟨(3, 2), m32⟩ := fun h => by
    have := hr ⟨(3, 1), m31⟩ ⟨(3, 2), m32⟩ rfl h
    simp at this
  -- the last two columns hold values ≤ 3
  have a4s : T ⟨(0, 4), m04⟩ = s := by
    have : T ⟨(0, 4), m04⟩ ∈ latin_column_symbols (latin_double_three_tail_shape 5) T 4 :=
      (mem_latin_column_symbols _ _ _ _).mpr ⟨_, rfl, rfl⟩
    rw [h4, Finset.mem_singleton] at this; exact this
  have a3le : T ⟨(0, 3), m03⟩ ≤ 3 := by
    have : T ⟨(0, 3), m03⟩ ∈ latin_column_symbols (latin_double_three_tail_shape 5) T 3 :=
      (mem_latin_column_symbols _ _ _ _).mpr ⟨_, rfl, rfl⟩
    rw [h3] at this; simp only [Finset.mem_sdiff, Finset.mem_Icc] at this; exact this.1.2
  have b3le : T ⟨(1, 3), m13⟩ ≤ 3 := by
    have : T ⟨(1, 3), m13⟩ ∈ latin_column_symbols (latin_double_three_tail_shape 5) T 3 :=
      (mem_latin_column_symbols _ _ _ _).mpr ⟨_, rfl, rfl⟩
    rw [h3] at this; simp only [Finset.mem_sdiff, Finset.mem_Icc] at this; exact this.1.2
  rw [Finset.mem_Icc] at hs
  obtain ⟨h5a, h4a⟩ := latin_double_three_tail_profile_base_five _ _ _ _ _ b00 b01 b02 ⟨b03.1, a3le⟩ (⟨b04.1, by rw [a4s]; exact hs.2⟩)
    n00_01 n00_02 n00_03 n00_04 n01_02
    n01_03 n01_04 n02_03 n02_04 n03_04
  have h4b := latin_double_three_tail_profile_base_four _ _ _ _ b10 b11 b12 ⟨b13.1, b3le⟩
    n10_11 n10_12 n10_13 n11_12 n11_13 n12_13
  rcases h5a with h5 | h5 | h5
  · have hne0 : T ⟨(0, 0), m00⟩ ≠ 4 := by rw [h5]; decide
    have hb0 : T ⟨(1, 0), m10⟩ ≠ 4 := by
      intro hb4
      rcases h4a with h | h | h
      · exact absurd h hne0
      · exact latin_double_three_tail_profile_base_no3 _ _ _ _ ⟨b02.1, latin_double_three_tail_profile_base_le3a _ _ _ b02.2 h5 h (Ne.symm n00_02) (Ne.symm n01_02)⟩ ⟨b12.1, latin_double_three_tail_profile_base_le3b _ _ b12.2 hb4 (Ne.symm n10_12)⟩ b22 b32 n02_12 n02_22 n02_32 n12_22 n12_32 n22_32
      · exact latin_double_three_tail_profile_base_no3 _ _ _ _ ⟨b01.1, latin_double_three_tail_profile_base_le3a _ _ _ b01.2 h5 h (Ne.symm n00_01) n01_02⟩ ⟨b11.1, latin_double_three_tail_profile_base_le3b _ _ b11.2 hb4 (Ne.symm n10_11)⟩ b21 b31 n01_11 n01_21 n01_31 n11_21 n11_31 n21_31
    have ha1 : T ⟨(0, 1), m01⟩ ≤ 4 := latin_double_three_tail_profile_base_le4 _ _ b01.2 h5 (Ne.symm n00_01)
    have ha2 : T ⟨(0, 2), m02⟩ ≤ 4 := latin_double_three_tail_profile_base_le4 _ _ b02.2 h5 (Ne.symm n00_02)
    refine ⟨s, Finset.mem_Icc.mpr hs, 0, by decide, ?_, ?_, ?_, ?_⟩
    · intro j hj
      rw [latin_double_three_tail_profile_base_col T j hj]
      interval_cases j
      · rw [if_pos rfl]; exact latin_double_three_tail_profile_base_set5 _ _ _ _ b00 b10 b20 b30 hne0 hb0 n00_10 n00_20 n00_30 n10_20 n10_30 n20_30
      · rw [if_neg (by decide)]; exact latin_double_three_tail_profile_base_set4 _ _ _ _ ⟨b01.1, ha1⟩ b11 ⟨b21.1, Nat.le_succ_of_le b21.2⟩ ⟨b31.1, Nat.le_succ_of_le b31.2⟩ n01_11 n01_21 n01_31 n11_21 n11_31 n21_31
      · rw [if_neg (by decide)]; exact latin_double_three_tail_profile_base_set4 _ _ _ _ ⟨b02.1, ha2⟩ b12 ⟨b22.1, Nat.le_succ_of_le b22.2⟩ ⟨b32.1, Nat.le_succ_of_le b32.2⟩ n02_12 n02_22 n02_32 n12_22 n12_32 n22_32
    · intro j hj1 hj2; exact absurd (lt_of_le_of_lt hj1 hj2) (by decide)
    · exact h3
    · exact h4
  · have hne1 : T ⟨(0, 1), m01⟩ ≠ 4 := by rw [h5]; decide
    have hb1 : T ⟨(1, 1), m11⟩ ≠ 4 := by
      intro hb4
      rcases h4a with h | h | h
      · exact latin_double_three_tail_profile_base_no3 _ _ _ _ ⟨b02.1, latin_double_three_tail_profile_base_le3a _ _ _ b02.2 h5 h (Ne.symm n01_02) (Ne.symm n00_02)⟩ ⟨b12.1, latin_double_three_tail_profile_base_le3b _ _ b12.2 hb4 (Ne.symm n11_12)⟩ b22 b32 n02_12 n02_22 n02_32 n12_22 n12_32 n22_32
      · exact absurd h hne1
      · exact latin_double_three_tail_profile_base_no3 _ _ _ _ ⟨b00.1, latin_double_three_tail_profile_base_le3a _ _ _ b00.2 h5 h n00_01 n00_02⟩ ⟨b10.1, latin_double_three_tail_profile_base_le3b _ _ b10.2 hb4 n10_11⟩ b20 b30 n00_10 n00_20 n00_30 n10_20 n10_30 n20_30
    have ha0 : T ⟨(0, 0), m00⟩ ≤ 4 := latin_double_three_tail_profile_base_le4 _ _ b00.2 h5 n00_01
    have ha2 : T ⟨(0, 2), m02⟩ ≤ 4 := latin_double_three_tail_profile_base_le4 _ _ b02.2 h5 (Ne.symm n01_02)
    refine ⟨s, Finset.mem_Icc.mpr hs, 1, by decide, ?_, ?_, ?_, ?_⟩
    · intro j hj
      rw [latin_double_three_tail_profile_base_col T j hj]
      interval_cases j
      · rw [if_neg (by decide)]; exact latin_double_three_tail_profile_base_set4 _ _ _ _ ⟨b00.1, ha0⟩ b10 ⟨b20.1, Nat.le_succ_of_le b20.2⟩ ⟨b30.1, Nat.le_succ_of_le b30.2⟩ n00_10 n00_20 n00_30 n10_20 n10_30 n20_30
      · rw [if_pos rfl]; exact latin_double_three_tail_profile_base_set5 _ _ _ _ b01 b11 b21 b31 hne1 hb1 n01_11 n01_21 n01_31 n11_21 n11_31 n21_31
      · rw [if_neg (by decide)]; exact latin_double_three_tail_profile_base_set4 _ _ _ _ ⟨b02.1, ha2⟩ b12 ⟨b22.1, Nat.le_succ_of_le b22.2⟩ ⟨b32.1, Nat.le_succ_of_le b32.2⟩ n02_12 n02_22 n02_32 n12_22 n12_32 n22_32
    · intro j hj1 hj2; exact absurd (lt_of_le_of_lt hj1 hj2) (by decide)
    · exact h3
    · exact h4
  · have hne2 : T ⟨(0, 2), m02⟩ ≠ 4 := by rw [h5]; decide
    have hb2 : T ⟨(1, 2), m12⟩ ≠ 4 := by
      intro hb4
      rcases h4a with h | h | h
      · exact latin_double_three_tail_profile_base_no3 _ _ _ _ ⟨b01.1, latin_double_three_tail_profile_base_le3a _ _ _ b01.2 h5 h n01_02 (Ne.symm n00_01)⟩ ⟨b11.1, latin_double_three_tail_profile_base_le3b _ _ b11.2 hb4 n11_12⟩ b21 b31 n01_11 n01_21 n01_31 n11_21 n11_31 n21_31
      · exact latin_double_three_tail_profile_base_no3 _ _ _ _ ⟨b00.1, latin_double_three_tail_profile_base_le3a _ _ _ b00.2 h5 h n00_02 n00_01⟩ ⟨b10.1, latin_double_three_tail_profile_base_le3b _ _ b10.2 hb4 n10_12⟩ b20 b30 n00_10 n00_20 n00_30 n10_20 n10_30 n20_30
      · exact absurd h hne2
    have ha0 : T ⟨(0, 0), m00⟩ ≤ 4 := latin_double_three_tail_profile_base_le4 _ _ b00.2 h5 n00_02
    have ha1 : T ⟨(0, 1), m01⟩ ≤ 4 := latin_double_three_tail_profile_base_le4 _ _ b01.2 h5 n01_02
    refine ⟨s, Finset.mem_Icc.mpr hs, 2, by decide, ?_, ?_, ?_, ?_⟩
    · intro j hj
      rw [latin_double_three_tail_profile_base_col T j hj]
      interval_cases j
      · rw [if_neg (by decide)]; exact latin_double_three_tail_profile_base_set4 _ _ _ _ ⟨b00.1, ha0⟩ b10 ⟨b20.1, Nat.le_succ_of_le b20.2⟩ ⟨b30.1, Nat.le_succ_of_le b30.2⟩ n00_10 n00_20 n00_30 n10_20 n10_30 n20_30
      · rw [if_neg (by decide)]; exact latin_double_three_tail_profile_base_set4 _ _ _ _ ⟨b01.1, ha1⟩ b11 ⟨b21.1, Nat.le_succ_of_le b21.2⟩ ⟨b31.1, Nat.le_succ_of_le b31.2⟩ n01_11 n01_21 n01_31 n11_21 n11_31 n21_31
      · rw [if_pos rfl]; exact latin_double_three_tail_profile_base_set5 _ _ _ _ b02 b12 b22 b32 hne2 hb2 n02_12 n02_22 n02_32 n12_22 n12_32 n22_32
    · intro j hj1 hj2; exact absurd (lt_of_le_of_lt hj1 hj2) (by decide)
    · exact h3
    · exact h4
