import AFTD.Prelude

/-!
# mondrian_rect_swap

Topic: combinatorics   Node: b4c5728b8923

Provenance: helper lemma. Helper for OP-280: modular shape inventories for the zero-defect question in arXiv:2610.19193, Section 1. The weighted row and prime-free count argument is developed here; it supplements the available-shape counting in arXiv:2311.02385, Section 3.

Exchange the x and y coordinate pairs of an integer rectangle.
-/

open scoped BigOperators

def mondrian_rect_swap (r : ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ :=
  (r.2.2.1, r.2.2.2, r.1, r.2.1)
