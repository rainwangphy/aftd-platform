import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphV3

/-!
# complete_four_not_induce_V3_maxDegree_le_two

Topic: graphs   Node: 6f4ff98a3692

Provenance: formalization of a published result. Source: arXiv:2610.21868, Section 4

In the complete simple graph on vertices Fin 4, the induced subgraph on the set of degree-3 vertices does not have maximum degree at most 2.
-/

/-- In the complete graph on four vertices, the induced subgraph on the degree-3 vertices does not have maximum degree at most 2. -/
theorem complete_four_not_induce_V3_maxDegree_le_two :
    ¬ ((⊤ : SimpleGraph (Fin 4)).induce (simple_graph_V3 (⊤ : SimpleGraph (Fin 4)) : Set (Fin 4))).maxDegree ≤ 2 := by
  decide
