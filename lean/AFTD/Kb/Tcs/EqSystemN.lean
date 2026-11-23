import AFTD.Prelude
import AFTD.Kb.Tcs.PmSumN
import AFTD.Kb.Tcs.AllEqual
import AFTD.Kb.Tcs.WeightsN

/-!
# EqSystemN

Topic: quantum   Node: 5c9ddfc6144b

Provenance: formalization of a published result. Source: arXiv:2611.26300

The proposition that an edge-weight function W : WeightsN N D α satisfies the monochromatic quantum graph system of equations: for every coloring ι : Fin N → Fin D, pmSumN N D W ι equals 1 if allEqual ι holds, and 0 otherwise.
-/

/-- The monochromatic quantum graph system of equations for weights W. -/
def EqSystemN {α : Type*} [Semiring α] (N D : ℕ) (W : WeightsN N D α) : Prop := open Classical in ∀ ι : Fin N → Fin D, pmSumN N D W ι = (if allEqual ι then (1 : α) else (0 : α))
