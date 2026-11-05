import AFTD.Prelude
import AFTD.Kb.Tcs.ColoredRootedTree

/-!
# instFintypeColoredRootedTree

Topic: data_structures   Node: 77bfb54c1b4b

Provenance: formalization of a published result. Source: arXiv:2611.03620 Section 2.1

The vertex set of a colored rooted tree is finite.
-/

/-- Fintype instance for the vertex type of a ColoredRootedTree. -/
instance instFintypeColoredRootedTree (T : ColoredRootedTree) : Fintype T.V := T.fintype
