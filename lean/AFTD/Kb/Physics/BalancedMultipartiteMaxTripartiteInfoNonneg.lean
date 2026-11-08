import AFTD.Prelude
import AFTD.Kb.Physics.BalancedMultipartiteMaxTripartiteInfo
import AFTD.Kb.Physics.SimpleGraphMaxTripartiteInfoNonneg

/-!
# balanced_multipartite_max_tripartite_info_nonneg

Topic: quantum_mechanics   Node: f94de1af3d08

Provenance: helper lemma. folklore

For any natural numbers k and s, the maximum tripartite information balanced_multipartite_max_tripartite_info k s of the complete multipartite graph with k parts of size s is at least 0.
-/

/-- The maximum tripartite information of any complete balanced multipartite graph is nonnegative. -/
theorem balanced_multipartite_max_tripartite_info_nonneg (k s : ℕ) :
    0 ≤ balanced_multipartite_max_tripartite_info k s := by
  unfold balanced_multipartite_max_tripartite_info
  exact simple_graph_max_tripartite_info_nonneg (SimpleGraph.completeMultipartiteGraph fun x : Fin k => Fin s)
