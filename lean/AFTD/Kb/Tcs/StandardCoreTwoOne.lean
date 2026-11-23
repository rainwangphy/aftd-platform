import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# standard_core_two_one

Topic: graphs   Node: 1d2e729d2392

Provenance: formalization of a published result. Source: arXiv:2611.18633 Theorem 4.3

The canonical 12-point set standard_core_two_one is the Finset (ℤ × ℤ) defined as ((Finset.Icc (0 : ℤ) 3) ×ˢ (Finset.Icc (0 : ℤ) 3)) \ {(0, 0), (0, 3), (3, 0), (3, 3)}.
-/

/-- The canonical 12-point set H₁ ∩ ℤ² in ℤ × ℤ (the 4 × 4 lattice square with its 4 corners removed). -/
def standard_core_two_one : Finset (ℤ × ℤ) := ((Finset.Icc (0 : ℤ) 3) ×ˢ (Finset.Icc (0 : ℤ) 3)) \ {(0, 0), (0, 3), (3, 0), (3, 3)}
