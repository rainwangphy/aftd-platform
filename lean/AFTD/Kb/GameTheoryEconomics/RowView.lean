import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RowLocalView

/-!
# rowView

Topic: combinatorial_games   Node: 1ef839a1f943

Provenance: formalization of a published result. Source: arXiv:2610.33032:178

Given a row seating of S sages represented as a permutation π with 2 ≤ S, the local view at position i is the sage π i along with their left neighbor (or none if i = 0) and their right neighbor (or none if i = S - 1).
-/

/-- The local view of the sage sitting at seat `i` in row seating `π`. -/
def rowView {S : ℕ} (hS : 2 ≤ S) (π : Equiv.Perm (Fin S)) (i : Fin S) : RowLocalView (Fin S) := (π i,
   if h0 : i.val = 0 then none else some (π ⟨i.val - 1, by omega⟩),
   if hlast : i.val = S - 1 then none else some (π ⟨i.val + 1, by omega⟩))
