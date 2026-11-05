import AFTD.Prelude
import AFTD.Kb.Tcs.ColoredRootedTree
import AFTD.Kb.Tcs.IntervalFamily
import AFTD.Kb.Tcs.ColoredTreeSubtree
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# has_contiguous_subtrees

Topic: data_structures   Node: cbe42e3a2c0c

Provenance: formalization of a published result. Source: arXiv:2611.03620 Proposition 3.3

An interval family has contiguous subtrees if the identifier image of every subtree is a closed integer interval.
-/

/-- Contiguous subtree property: each subtree occupies consecutive integer positions. -/
def has_contiguous_subtrees {T : ColoredRootedTree} {R : ℕ} (F : IntervalFamily T R) : Prop := ∀ v : T.V, ∃ a b : ℤ, F.id '' (colored_tree_subtree T v) = Set.Icc a b
