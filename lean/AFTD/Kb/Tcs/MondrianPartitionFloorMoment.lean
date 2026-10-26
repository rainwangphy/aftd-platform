import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianPartitionHorizontalMoment
import AFTD.Kb.Tcs.MondrianRectWidth

/-!
# mondrian_partition_floor_moment

Topic: combinatorics   Node: 73f2015eb68e

Provenance: helper lemma. Helper for OP-280: modular shape inventories for the zero-defect question in arXiv:2610.19193, Section 1. The weighted row and prime-free count argument is developed here; it supplements the available-shape counting in arXiv:2311.02385, Section 3.

For every natural q, the sum of width times the difference of the quotient y coordinates across each tile in an admissible n-square partition is n times floor(n/q), with integer-valued differences.
-/

open scoped BigOperators

theorem mondrian_partition_floor_moment (n q : ℕ)
    (P : List (ℕ × ℕ × ℕ × ℕ)) (hp : mondrian_is_partition n P) :
    (P.map (fun r => (mondrian_rect_width r : ℤ) *
      (((r.2.2.2 / q : ℕ) : ℤ) - ((r.2.2.1 / q : ℕ) : ℤ)))).sum =
      (n : ℤ) * (n / q : ℕ) := by
  have hh := mondrian_partition_horizontal_moment n P hp (fun y => ((y / q : ℕ) : ℤ))
  simpa using hh
