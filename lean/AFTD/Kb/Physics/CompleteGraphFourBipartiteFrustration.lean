import AFTD.Prelude
import AFTD.Kb.Physics.BipartiteFrustration

/-!
# complete_graph_four_bipartite_frustration

Topic: statistical_mechanics   Node: 688175c71e29

Provenance: original. Related work: arXiv:2204.00875

The bipartite frustration index of the complete graph K_4 on four vertices is equal to 2.
-/

/-- The bipartite frustration index of K_4 is 2. -/
theorem complete_graph_four_bipartite_frustration :
    bipartite_frustration (SimpleGraph.completeGraph (Fin 4)) = 2 := by
  decide
