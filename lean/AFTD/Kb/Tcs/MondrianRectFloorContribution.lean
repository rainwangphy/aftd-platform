import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianRectArea
import AFTD.Kb.Tcs.MondrianRectHeight
import AFTD.Kb.Tcs.MondrianRectWidth

/-!
# mondrian_rect_floor_contribution

Topic: combinatorics   Node: ca5f5c606263

Provenance: helper lemma. Helper for OP-280: modular shape inventories for the zero-defect question in arXiv:2610.19193, Section 1. The weighted row and prime-free count argument is developed here; it supplements the available-shape counting in arXiv:2311.02385, Section 3.

When positive q divides a rectangle height, its width times the integer difference of quotient y coordinates is its area divided by q.
-/

open scoped BigOperators

theorem mondrian_rect_floor_contribution (r : ℕ × ℕ × ℕ × ℕ)
    (hy : r.2.2.1 ≤ r.2.2.2) (q : ℕ) (hq : 0 < q)
    (hd : q ∣ mondrian_rect_height r) :
    (mondrian_rect_width r : ℤ) *
      (((r.2.2.2 / q : ℕ) : ℤ) - ((r.2.2.1 / q : ℕ) : ℤ)) =
      ((mondrian_rect_area r / q : ℕ) : ℤ) := by
  obtain ⟨d, hd⟩ := hd
  have hy1 : r.2.2.2 = r.2.2.1 + q * d := by
    dsimp [mondrian_rect_height] at hd
    omega
  have hdiv : mondrian_rect_area r / q = mondrian_rect_width r * d := by
    rw [mondrian_rect_area, hd,
      show mondrian_rect_width r * (q * d) = (mondrian_rect_width r * d) * q by ring,
      Nat.mul_div_cancel _ hq]
  rw [hdiv, hy1, Nat.add_mul_div_left _ _ hq]
  push_cast
  ring
