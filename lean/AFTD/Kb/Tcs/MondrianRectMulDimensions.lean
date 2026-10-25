import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianRectHeight
import AFTD.Kb.Tcs.MondrianRectMul
import AFTD.Kb.Tcs.MondrianRectWidth

/-!
# mondrian_rect_mul_dimensions

Topic: combinatorics   Node: ae794df4b06a

Provenance: helper lemma. Helper for OP-280 and mondrian_perfect_partition_large_prime_iff. Related work: arXiv:2610.19193, Section 1 (perfect partitions and scaling); arXiv:2007.09639, Theorem 4.1 (available shapes and prime-power exclusions).

Multiplying coordinates by a multiplies both side lengths by a.
-/

theorem mondrian_rect_mul_dimensions (a : ℕ) (r : ℕ × ℕ × ℕ × ℕ) :
    mondrian_rect_width (mondrian_rect_mul a r) = a * mondrian_rect_width r ∧
      mondrian_rect_height (mondrian_rect_mul a r) = a * mondrian_rect_height r := by
  simp [mondrian_rect_mul, mondrian_rect_width, mondrian_rect_height,
    Nat.mul_sub_left_distrib]
