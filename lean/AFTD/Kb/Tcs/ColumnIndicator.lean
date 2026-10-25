import AFTD.Prelude

/-!
# column_indicator

Topic: quantum   Node: 839c4c923803

Provenance: formalization of a published result. Source: arXiv:2610.09341, Section 3.1

The column indicator of an s by n matrix over ZMod 2 evaluates to 1 at a vector if it appears as a column of the matrix, and 0 otherwise.
-/

open scoped Classical
open Matrix in
/-- The column indicator function of an s by n matrix over ZMod 2. -/
noncomputable def column_indicator {s n : ℕ} (S : Matrix (Fin s) (Fin n) (ZMod 2)) : (Fin s → ZMod 2) → ZMod 2 := fun β => if ∃ j : Fin n, Sᵀ j = β then 1 else 0
