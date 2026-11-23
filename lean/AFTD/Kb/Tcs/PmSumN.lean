import AFTD.Prelude
import AFTD.Kb.Tcs.PmSumList
import AFTD.Kb.Tcs.Vertices
import AFTD.Kb.Tcs.WeightsN

/-!
# pmSumN

Topic: quantum   Node: ecf7645ca0ca

Provenance: formalization of a published result. Source: arXiv:2611.26300

Given a semiring α, weights W : WeightsN N D α, and a coloring ι : Fin N → Fin D, pmSumN N D W ι is pmSumList W ι (vertices N), the sum over all perfect matchings of K_N.
-/

/-- The coherent amplitude for a colouring ι given by the sum over all perfect matchings of K_N. -/
def pmSumN {α : Type*} [Semiring α] (N D : ℕ) (W : WeightsN N D α) (ι : Fin N → Fin D) : α := pmSumList W ι (vertices N)
