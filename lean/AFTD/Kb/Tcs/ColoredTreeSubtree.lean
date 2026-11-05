import AFTD.Prelude
import AFTD.Kb.Tcs.ColoredRootedTree
import AFTD.Kb.Tcs.InstPartialOrderColoredRootedTree

/-!
# colored_tree_subtree

Topic: data_structures   Node: 5036d6870db4

Provenance: formalization of a published result. Source: arXiv:2611.03620 Section 2

The subtree rooted at vertex v consists of all descendants of v in the tree.
-/

/-- The subtree rooted at a vertex v in a ColoredRootedTree. -/
def colored_tree_subtree (T : ColoredRootedTree) (v : T.V) : Set T.V := Set.Ici v
