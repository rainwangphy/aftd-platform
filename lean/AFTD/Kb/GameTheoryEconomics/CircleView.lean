import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CircleLocalView

/-!
# circleView

Topic: combinatorial_games   Node: d6336d8f1d28

Provenance: formalization of a published result. Source: arXiv:2610.33032, Section 2

Given an implicit natural number S, a hypothesis hS : 3 ≤ S, a permutation π : Equiv.Perm (Fin S), and a seat index i : Fin S, circleView hS π i is defined as the triple (π i, π (i - 1), π (i + 1)) in CircleLocalView (Fin S), where subtraction and addition on Fin S are modulo S.
-/

/-- Local view at seat i in a circular seating π. -/
def circleView {S : ℕ} (hS : 3 ≤ S) (π : Equiv.Perm (Fin S)) (i : Fin S) : CircleLocalView (Fin S) :=
  have : NeZero S := ⟨by omega⟩
  (π i, π (i - 1), π (i + 1))
