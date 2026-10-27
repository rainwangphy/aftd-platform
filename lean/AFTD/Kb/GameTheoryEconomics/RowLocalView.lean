import AFTD.Prelude

/-!
# RowLocalView

Topic: combinatorial_games   Node: 017f776909f0

Provenance: formalization of a published result. Source: arXiv:2610.33032:178

For sages of type α, a local view in an unlabeled row consists of the sage's own identity together with an optional left neighbor and an optional right neighbor.
-/

/-- A local view in the anonymous-slip row puzzle: the sage and their optional left and right neighbors. -/
def RowLocalView (α : Type) : Type := α × Option α × Option α
