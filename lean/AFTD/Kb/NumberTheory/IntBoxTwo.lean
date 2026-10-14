import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# int_box_two

Topic: elementary_number_theory   Node: 43064acfc0f6

Provenance: formalization of a published result. Source: arXiv:2610.16562 (The Davenport constant of low-dimensional boxes), Sec. 1 (the boxes ⟦−m, m⟧^d).

The two-dimensional integer box ⟦−m, m⟧² = {(x, y) ∈ ℤ² : |x|, |y| ≤ m}.
-/

/-- The two-dimensional integer box `⟦-m, m⟧²`. -/
noncomputable def int_box_two (m : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-(m : ℤ)) m ×ˢ Finset.Icc (-(m : ℤ)) m
