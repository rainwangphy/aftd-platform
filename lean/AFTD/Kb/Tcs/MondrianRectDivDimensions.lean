import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianRectDiv
import AFTD.Kb.Tcs.MondrianRectHeight
import AFTD.Kb.Tcs.MondrianRectWidth
import AFTD.Kb.Tcs.MondrianSubDivMul

/-!
# mondrian_rect_div_dimensions

Topic: combinatorics   Node: 592f7e07f0ba

Provenance: helper lemma. Helper for OP-280 and mondrian_perfect_partition_large_prime_iff. Related work: arXiv:2610.19193, Section 1 (perfect partitions and scaling); arXiv:2007.09639, Theorem 4.1 (available shapes and prime-power exclusions).

Dividing coordinates of a positive rectangle whose side lengths are multiples of a divides its width and height exactly by a.
-/

theorem mondrian_rect_div_dimensions (a : ℕ) (ha : 0 < a)
    (r : ℕ × ℕ × ℕ × ℕ)
    (hx : r.1 < r.2.1) (hy : r.2.2.1 < r.2.2.2)
    (hw : a ∣ mondrian_rect_width r) (hh : a ∣ mondrian_rect_height r) :
    a * mondrian_rect_width (mondrian_rect_div a r) = mondrian_rect_width r ∧
      a * mondrian_rect_height (mondrian_rect_div a r) = mondrian_rect_height r := by
  exact ⟨mondrian_sub_div_mul a _ _ ha (Nat.le_of_lt hx) hw,
    mondrian_sub_div_mul a _ _ ha (Nat.le_of_lt hy) hh⟩
