import AFTD.Prelude
import AFTD.Kb.Tcs.HasMonochromaticBox

/-!
# grid_ramsey_prop

Topic: combinatorics   Node: 227f31946812

Provenance: formalization of a published result. Source: arXiv:2611.17378, Section 4

The grid Ramsey property `grid_ramsey_prop d c n` holds if every coloring `χ : (Fin d → Fin n) → Fin c` contains a monochromatic box.
-/

/-- The property that every `c`-coloring of `Fin d → Fin n` contains a monochromatic box. -/
def grid_ramsey_prop (d c n : ℕ) : Prop := ∀ χ : (Fin d → Fin n) → Fin c, has_monochromatic_box d c n χ
