import AFTD.Prelude
import AFTD.Kb.Tcs.ColoredRootedTree

/-!
# instPartialOrderColoredRootedTree

Topic: data_structures   Node: 2e50a4bb76df

Provenance: formalization of a published result. Source: arXiv:2611.03620 Section 2.1

The ancestorship relation on the vertices of a colored rooted tree forms a partial order.
-/

/-- PartialOrder instance for the vertex type of a ColoredRootedTree. -/
instance instPartialOrderColoredRootedTree (T : ColoredRootedTree) : PartialOrder T.V := T.partialOrder
