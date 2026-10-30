import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CircleLocalView
import AFTD.Kb.GameTheoryEconomics.CircleView

/-!
# circleMultiset

Topic: combinatorial_games   Node: e761b2c7d0c9

Provenance: formalization of a published result. Source: arXiv:2610.33032, Section 2

Given an implicit natural number S and an implicit type α, a hypothesis hS : 3 ≤ S, a protocol p : CircleLocalView (Fin S) → α, and a permutation π : Equiv.Perm (Fin S), circleMultiset hS p π is the multiset Finset.univ.val.map (fun i => p (circleView hS π i)).
-/

/-- The multiset of symbols announced by sages in a circular seating. -/
def circleMultiset {S : ℕ} {α : Type*} (hS : 3 ≤ S) (p : CircleLocalView (Fin S) → α) (π : Equiv.Perm (Fin S)) : Multiset α := Finset.univ.val.map (fun i => p (circleView hS π i))
