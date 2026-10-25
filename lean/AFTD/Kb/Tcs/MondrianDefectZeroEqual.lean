import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianDefect
import AFTD.Kb.Tcs.MondrianRectArea

/-!
# mondrian_defect_zero_equal

Topic: combinatorics   Node: 3dab5ef3d7b3

Provenance: helper lemma. arXiv:2610.19193, Section 1, and arXiv:2311.02385, Section 3 (available integer dimension pairs); helper for OP-280 and mondrian_no_perfect_partition.

Any two rectangles in a list of defect zero have equal area.
-/

theorem mondrian_defect_zero_equal (P : List (ℕ × ℕ × ℕ × ℕ))
    (h : mondrian_defect P = 0) (r s : ℕ × ℕ × ℕ × ℕ)
    (hr : r ∈ P) (hs : s ∈ P) : mondrian_rect_area r = mondrian_rect_area s := by
  have hr' : mondrian_rect_area r ∈ P.map mondrian_rect_area := List.mem_map.mpr ⟨r, hr, rfl⟩
  have hs' : mondrian_rect_area s ∈ P.map mondrian_rect_area := List.mem_map.mpr ⟨s, hs, rfl⟩
  cases hmax : (P.map mondrian_rect_area).max? with
  | none =>
    have := List.max?_eq_none_iff.mp hmax
    rw [this] at hr'
    simp at hr'
  | some a =>
    cases hmin : (P.map mondrian_rect_area).min? with
    | none =>
      have := List.min?_eq_none_iff.mp hmin
      rw [this] at hr'
      simp at hr'
    | some b =>
      have hmax' := List.max?_eq_some_iff.mp hmax
      have hmin' := List.min?_eq_some_iff.mp hmin
      have h1 := hmax'.2 _ hr'
      have h2 := hmax'.2 _ hs'
      have h3 := hmin'.2 _ hr'
      have h4 := hmin'.2 _ hs'
      simp only [mondrian_defect, hmax, hmin, Option.getD_some,
        Nat.sub_eq_zero_iff_le] at h
      omega
