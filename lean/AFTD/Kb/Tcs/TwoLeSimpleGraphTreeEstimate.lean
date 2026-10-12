import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTreeEstimate

/-!
# two_le_simple_graph_tree_estimate

Topic: graphs   Node: e0c9b0f7ac4f

Provenance: helper lemma. Sanity lemma for simple_graph_tree_estimate (arXiv:2610.09650 (The Almost Stacked Hypothesis: A Conjectural Analogue of Sjöstrand's Cover Pebbling Theorem), Definition 5.1).

The tree estimate is at least 2.
-/

theorem two_le_simple_graph_tree_estimate {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] : 2 ≤ simple_graph_tree_estimate T :=
  le_max_left _ _
