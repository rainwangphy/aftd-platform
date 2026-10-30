import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CircleLocalView
import AFTD.Kb.GameTheoryEconomics.CircleView

/-!
# circleViewOfSage

Topic: combinatorial_games   Node: af4243a0c82a

Provenance: formalization of a published result. Source: arXiv:2610.33032, Section 2

Given an implicit natural number S, a hypothesis hS : 3 ≤ S, a permutation π : Equiv.Perm (Fin S), and a sage x : Fin S, circleViewOfSage hS π x is circleView hS π (π.symm x).
-/

/-- The local view of a given sage x in a circular seating π. -/
def circleViewOfSage {S : ℕ} (hS : 3 ≤ S) (π : Equiv.Perm (Fin S)) (x : Fin S) : CircleLocalView (Fin S) := circleView hS π (π.symm x)
