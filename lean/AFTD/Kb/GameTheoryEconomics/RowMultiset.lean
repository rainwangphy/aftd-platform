import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RowLocalView
import AFTD.Kb.GameTheoryEconomics.RowView

/-!
# rowMultiset

Topic: combinatorial_games   Node: e9d9f1319740

Provenance: formalization of a published result. Source: arXiv:2610.33032:180

Given a hypothesis 2 ≤ S, the public multiset of values produced by a protocol p : RowLocalView (Fin S) → α on a row seating π : Equiv.Perm (Fin S) is the multiset obtained by mapping fun i => p (rowView hS π i) over all seats i : Fin S in Finset.univ.val.
-/

/-- The public multiset of values produced by a protocol on a row seating. -/
def rowMultiset {S : ℕ} {α : Type*} (hS : 2 ≤ S) (p : RowLocalView (Fin S) → α) (π : Equiv.Perm (Fin S)) : Multiset α := Finset.univ.val.map (fun i => p (rowView hS π i))
