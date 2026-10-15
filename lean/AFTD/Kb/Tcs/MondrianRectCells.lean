import AFTD.Prelude

/-!
# mondrian_rect_cells

Topic: combinatorics   Node: 49ea219d0e4e

Provenance: formalization of a published result. Source: arXiv:2610.19193 (A Bounded-Defect Construction for the Mondrian Art Problem), Sec. 1 (rectangles with integer corners in the canvas [0,n]×[0,n]); the cell encoding is chosen here: integer rectangles have disjoint interiors iff their cell sets are disjoint.

The unit cells [i,i+1]×[j,j+1] of the integer rectangle [x₀,x₁]×[y₀,y₁], recorded as r = (x₀, x₁, y₀, y₁); a cell is named by its lower-left corner (i, j).
-/

/-- Unit cells of the rectangle `[x₀,x₁]×[y₀,y₁]`, given as `(x₀, x₁, y₀, y₁)`. -/
def mondrian_rect_cells (r : ℕ × ℕ × ℕ × ℕ) : Finset (ℕ × ℕ) :=
  Finset.Ico r.1 r.2.1 ×ˢ Finset.Ico r.2.2.1 r.2.2.2
