import AFTD.Prelude
import AFTD.Kb.Tcs.PlaneTreeMirror
import AFTD.Kb.Tcs.PlaneTree
import AFTD.Kb.Tcs.InMLeafyTrees

/-!
# mirror_symmetric_m_leafy_trees

Topic: combinatorics   Node: f9e733f8d60e

Provenance: formalization of a published result. Source: arXiv:2611.10154 Sec. 2.3

The set mirror_symmetric_m_leafy_trees m n consists of all trees t in in_m_leafy_trees m n satisfying plane_tree_mirror t = t.
-/

/-- The set of mirror-symmetric trees in in_m_leafy_trees m n. -/
def mirror_symmetric_m_leafy_trees (m n : ℕ) : Set PlaneTree := {t : PlaneTree | in_m_leafy_trees m n t ∧ plane_tree_mirror t = t}
