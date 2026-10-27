import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RowLocalView
import AFTD.Kb.GameTheoryEconomics.RowView

/-!
# rowViewOfSage

Topic: combinatorial_games   Node: 29cd7464cf59

Provenance: formalization of a published result. Source: arXiv:2610.33032:178

The local view of sage x in a row seating π is the local view at the position π.symm x occupied by x.
-/

/-- The local view of sage `x` in row seating `π`. -/
def rowViewOfSage {S : ℕ} (hS : 2 ≤ S) (π : Equiv.Perm (Fin S)) (x : Fin S) : RowLocalView (Fin S) := rowView hS π (π.symm x)
