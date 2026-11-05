import AFTD.Prelude
import AFTD.Kb.Tcs.ColoredRootedTree

/-!
# instDecEqColoredRootedTree

Topic: data_structures   Node: c900dd89e8b0

Provenance: formalization of a published result. Source: arXiv:2611.03620 Section 2.1

Equality on the vertices of a colored rooted tree is decidable.
-/

/-- DecidableEq instance for the vertex type of a ColoredRootedTree. -/
instance instDecEqColoredRootedTree (T : ColoredRootedTree) : DecidableEq T.V := T.decEq
