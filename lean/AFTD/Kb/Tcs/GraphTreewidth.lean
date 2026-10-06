import AFTD.Prelude
import AFTD.Kb.Tcs.HasTreeDecompositionOfWidthLe

/-!
# graph_treewidth

Topic: proof_complexity   Node: 6a07987f046a

Provenance: formalization of a published result. Source: Short Resolution Refutations for CNFs with Bounded Weighted Incidence Treewidth, arXiv:2610.02047, Sec. 3.2 (treewidth)

The treewidth of a graph: the least w such that it has a tree decomposition of width at most w.
-/

/-- The treewidth of a graph: the least width of a tree decomposition. -/
noncomputable def graph_treewidth {α : Type*} (G : SimpleGraph α) : ℕ :=
  sInf {w | has_tree_decomposition_of_width_le G w}
