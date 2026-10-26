import AFTD.Prelude

/-!
# simple_graph_prism

Topic: graphs   Node: e8500cd6fe8a

Provenance: formalization of a published result. Source: arXiv:2610.18463 Question 5.4

The prism graph P₁ □ C_n on vertex set Fin 2 × Fin n, defined as the Cartesian box product of the 2-vertex complete graph K₂ (the path P₁) and the cycle graph C_n.
-/

/-- The prism graph P₁ □ C_n as the Cartesian box product of K₂ and C_n. -/
def simple_graph_prism (n : ℕ) : SimpleGraph (Fin 2 × Fin n) :=
  SimpleGraph.completeGraph (Fin 2) □ SimpleGraph.cycleGraph n
