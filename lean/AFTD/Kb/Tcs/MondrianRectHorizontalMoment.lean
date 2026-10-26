import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianRectCells
import AFTD.Kb.Tcs.MondrianRectWidth

/-!
# mondrian_rect_horizontal_moment

Topic: combinatorics   Node: 7acdf84f1bb3

Provenance: helper lemma. Helper for OP-280: modular shape inventories for the zero-defect question in arXiv:2610.19193, Section 1. The weighted row and prime-free count argument is developed here; it supplements the available-shape counting in arXiv:2311.02385, Section 3.

The sum over a rectangle of the row increment f(y+1)-f(y) equals its width times the difference between f at its upper and lower y coordinates.
-/

open scoped BigOperators

theorem mondrian_rect_horizontal_moment (r : ℕ × ℕ × ℕ × ℕ)
    (hy : r.2.2.1 ≤ r.2.2.2) (f : ℕ → ℤ) :
    ∑ c ∈ mondrian_rect_cells r, (f (c.2 + 1) - f c.2) =
      (mondrian_rect_width r : ℤ) * (f r.2.2.2 - f r.2.2.1) := by
  simp only [mondrian_rect_cells, Finset.sum_product,
    Finset.sum_Ico_sub f hy, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul,
    mondrian_rect_width]
