import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# lattice_ball_one

Topic: graphs   Node: 11a80d699438

Provenance: formalization of a published result. Source: arXiv:2611.18633 Section 1

For p : ℤ × ℤ, lattice_ball_one p is the Finset (ℤ × ℤ) defined as the Cartesian product of the closed integer intervals (Finset.Icc (p.1 - 1) (p.1 + 1)) and (Finset.Icc (p.2 - 1) (p.2 + 1)).
-/

/-- The closed radius-one sup-norm ball around a point in ℤ × ℤ as a Finset. -/
def lattice_ball_one (p : ℤ × ℤ) : Finset (ℤ × ℤ) := (Finset.Icc (p.1 - 1) (p.1 + 1)) ×ˢ (Finset.Icc (p.2 - 1) (p.2 + 1))
