import AFTD.Prelude
import AFTD.Kb.Tcs.PmSumListAux
import AFTD.Kb.Tcs.WeightsN

/-!
# pmSumList

Topic: quantum   Node: 36e7e48bba7a

Provenance: formalization of a published result. Source: arXiv:2611.26300

Given a semiring α, weights W : WeightsN N D α, a vertex coloring ι : Fin N → Fin D, and a vertex list L : List (Fin N), pmSumList W ι L is the value pmSumListAux W ι L.length L.
-/

/-- Sum over all perfect matchings of a list of vertices. -/
def pmSumList {α : Type*} [Semiring α] {N D : ℕ} (W : WeightsN N D α) (ι : Fin N → Fin D) (L : List (Fin N)) : α := pmSumListAux W ι L.length L
