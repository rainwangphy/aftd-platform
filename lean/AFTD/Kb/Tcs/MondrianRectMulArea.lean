import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianRectArea
import AFTD.Kb.Tcs.MondrianRectMul
import AFTD.Kb.Tcs.MondrianRectMulDimensions
import AFTD.Kb.Tcs.MondrianRectHeight
import AFTD.Kb.Tcs.MondrianRectWidth

/-!
# mondrian_rect_mul_area

Topic: combinatorics   Node: 93cb193d8383

Provenance: helper lemma. Helper for OP-280 and mondrian_perfect_partition_large_prime_iff. Related work: arXiv:2610.19193, Section 1 (perfect partitions and scaling); arXiv:2007.09639, Theorem 4.1 (available shapes and prime-power exclusions).

Multiplying rectangle coordinates by a multiplies its area by a squared.
-/

theorem mondrian_rect_mul_area (a : ℕ) (r : ℕ × ℕ × ℕ × ℕ) :
    mondrian_rect_area (mondrian_rect_mul a r) = a ^ 2 * mondrian_rect_area r := by
  obtain ⟨hw, hh⟩ := mondrian_rect_mul_dimensions a r
  simp only [mondrian_rect_area, hw, hh]
  ring
