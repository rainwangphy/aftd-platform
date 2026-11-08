import AFTD.Prelude
import AFTD.Kb.Physics.SimpleGraphMaxTripartiteInfo

/-!
# balanced_multipartite_max_tripartite_info

Topic: quantum_mechanics   Node: 5c0e8249f617

Provenance: original. Related work: arXiv:2511.19585, 'Monogamy of Mutual Information in Graph States'

For natural numbers k and s, balanced_multipartite_max_tripartite_info k s is the maximum tripartite information simple_graph_max_tripartite_info of the complete multipartite graph with k parts each of size s.
-/

/-- Maximum tripartite information M(k, s) over all four-partitions of the complete balanced multipartite graph with k parts each of size s. -/
noncomputable def balanced_multipartite_max_tripartite_info (k s : ℕ) : ℤ := simple_graph_max_tripartite_info (SimpleGraph.completeMultipartiteGraph (fun _ : Fin k => Fin s))
