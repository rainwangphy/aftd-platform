import AFTD.Prelude
import AFTD.Kb.Tcs.PlaneTree
import AFTD.Kb.Tcs.InMLeafyTrees

/-!
# MLeafyTree

Topic: combinatorics   Node: 20e691626218

Provenance: formalization of a published result. Source: arXiv:2611.10154 Def. 2.2

The type MLeafyTree m n is the subtype of plane trees belonging to LT_n^m.
-/

/-- The type of m-leafy trees with n internal vertices and mn + 1 leaves. -/
abbrev MLeafyTree (m n : ℕ) : Type := { t : PlaneTree // in_m_leafy_trees m n t }
