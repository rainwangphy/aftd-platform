import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianDefect
import AFTD.Kb.Tcs.MondrianSevenRects
import AFTD.Kb.Tcs.MondrianRectArea

/-!
# mondrian_seven_rects_defect

Topic: combinatorics   Node: 037900eb1cee

Provenance: helper lemma. arXiv:2610.19193 (A Bounded-Defect Construction for the Mondrian Art Problem), Proposition 1, formula (4); serves mondrian_seven_rects_partition_defect.

With E = p² − 19q², the defect of the seven-rectangle dissection is 140|E|.
-/

theorem mondrian_seven_rects_defect (p q : ℕ) (hpar : p % 2 = q % 2) (hqp : q < p)
    (hp : p < 7 * q) :
    (mondrian_defect (mondrian_seven_rects p q) : ℤ) = 140 * |(p : ℤ) ^ 2 - 19 * (q : ℤ) ^ 2| := by
  obtain ⟨s, rfl⟩ : ∃ s, p = q + 2 * s := ⟨(p - q) / 2, by omega⟩
  have hs3 : s < 3 * q := by omega
  have hmap : (mondrian_seven_rects (q + 2 * s) q).map mondrian_rect_area =
      [(63 * q + 14 * s) * (35 * q - 10 * s), (42 * q - 14 * s) * (60 * q + 15 * s),
       (56 * q + 14 * s) * (45 * q - 15 * s), (49 * q - 14 * s) * (45 * q + 10 * s),
       (63 * q) * (25 * q), (14 * s) * (25 * q + 25 * s), (14 * q + 14 * s) * (25 * s)] := by
    simp only [mondrian_seven_rects, List.map_cons, List.map_nil, mondrian_rect_area,
      mondrian_rect_width, mondrian_rect_height, List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> congr 1 <;> omega
  rw [mondrian_defect, hmap]
  have c1 : 10 * s ≤ 35 * q := by omega
  have c2 : 14 * s ≤ 42 * q := by omega
  have c3 : 15 * s ≤ 45 * q := by omega
  have c4 : 14 * s ≤ 49 * q := by omega
  -- F = 2 s² + 2 q s − 9 q², so that p² − 19 q² = 2F
  obtain ⟨F, hF⟩ : ∃ F : ℤ, F = 2 * (s : ℤ) ^ 2 + 2 * (q : ℤ) * s - 9 * (q : ℤ) ^ 2 := ⟨_, rfl⟩
  have hE : ((q + 2 * s : ℕ) : ℤ) ^ 2 - 19 * (q : ℤ) ^ 2 = 2 * F := by rw [hF]; push_cast; ring
  rw [hE]
  have A1 : (((63 * q + 14 * s) * (35 * q - 10 * s) : ℕ) : ℤ) = 1575 * (q : ℤ) ^ 2 - 70 * F := by
    rw [hF]; push_cast [Nat.cast_sub c1]; ring
  have A2 : (((42 * q - 14 * s) * (60 * q + 15 * s) : ℕ) : ℤ) = 1575 * (q : ℤ) ^ 2 - 105 * F := by
    rw [hF]; push_cast [Nat.cast_sub c2]; ring
  have A3 : (((56 * q + 14 * s) * (45 * q - 15 * s) : ℕ) : ℤ) = 1575 * (q : ℤ) ^ 2 - 105 * F := by
    rw [hF]; push_cast [Nat.cast_sub c3]; ring
  have A4 : (((49 * q - 14 * s) * (45 * q + 10 * s) : ℕ) : ℤ) = 1575 * (q : ℤ) ^ 2 - 70 * F := by
    rw [hF]; push_cast [Nat.cast_sub c4]; ring
  have A5 : (((63 * q) * (25 * q) : ℕ) : ℤ) = 1575 * (q : ℤ) ^ 2 := by push_cast; ring
  have A6 : (((14 * s) * (25 * q + 25 * s) : ℕ) : ℤ) = 1575 * (q : ℤ) ^ 2 + 175 * F := by
    rw [hF]; push_cast; ring
  have A7 : (((14 * q + 14 * s) * (25 * s) : ℕ) : ℤ) = 1575 * (q : ℤ) ^ 2 + 175 * F := by
    rw [hF]; push_cast; ring
  generalize (63 * q + 14 * s) * (35 * q - 10 * s) = x1 at A1 ⊢
  generalize (42 * q - 14 * s) * (60 * q + 15 * s) = x2 at A2 ⊢
  generalize (56 * q + 14 * s) * (45 * q - 15 * s) = x3 at A3 ⊢
  generalize (49 * q - 14 * s) * (45 * q + 10 * s) = x4 at A4 ⊢
  generalize (63 * q) * (25 * q) = x5 at A5 ⊢
  generalize (14 * s) * (25 * q + 25 * s) = x6 at A6 ⊢
  generalize (14 * q + 14 * s) * (25 * s) = x7 at A7 ⊢
  clear hF hE
  generalize (q : ℤ) ^ 2 = Q at *
  rcases le_or_gt 0 F with hF0 | hF0
  · have hmax : [x1, x2, x3, x4, x5, x6, x7].max? = some x6 := by
      rw [List.max?_eq_some_iff']
      refine ⟨by simp, ?_⟩
      intro b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    have hmin : [x1, x2, x3, x4, x5, x6, x7].min? = some x2 := by
      rw [List.min?_eq_some_iff']
      refine ⟨by simp, ?_⟩
      intro b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    rw [hmax, hmin, Option.getD_some, Option.getD_some, abs_of_nonneg (by omega)]
    omega
  · have hmax : [x1, x2, x3, x4, x5, x6, x7].max? = some x2 := by
      rw [List.max?_eq_some_iff']
      refine ⟨by simp, ?_⟩
      intro b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    have hmin : [x1, x2, x3, x4, x5, x6, x7].min? = some x6 := by
      rw [List.min?_eq_some_iff']
      refine ⟨by simp, ?_⟩
      intro b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    rw [hmax, hmin, Option.getD_some, Option.getD_some, abs_of_neg (by omega)]
    omega
