import AFTD.Prelude
import AFTD.Kb.Tcs.IsBox

/-!
# has_monochromatic_box

Topic: combinatorics   Node: fd7ed9f48205

Provenance: formalization of a published result. Source: arXiv:2611.17378, Section 4

A coloring `χ : (Fin d → Fin n) → Fin c` contains a monochromatic box if there exists a box `B` and a color `col : Fin c` such that every point `x ∈ B` has color `χ x = col`.
-/

/-- A coloring contains a monochromatic box if all points of some box have the same color. -/
def has_monochromatic_box (d c n : ℕ) (χ : (Fin d → Fin n) → Fin c) : Prop := ∃ B : Finset (Fin d → Fin n), is_box d B ∧ ∃ col : Fin c, ∀ x ∈ B, χ x = col
