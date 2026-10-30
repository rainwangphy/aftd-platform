import AFTD.Prelude

/-!
# cartesian_power_graph

Topic: graphs   Node: ef0c74744fbd

Provenance: formalization of a published result. Source: arXiv:2610.36620, Section 3.1

The n-fold Cartesian power of a graph G, with vertices given by functions from Fin n to V, where two vertices are adjacent if and only if they differ in exactly one coordinate and are adjacent in G at that coordinate.
-/

/-- The n-fold Cartesian power of a simple graph. -/
def cartesian_power_graph {V : Type*} (G : SimpleGraph V) (n : ℕ) : SimpleGraph (Fin n → V) := SimpleGraph.fromRel (fun f g => ∃ i : Fin n, G.Adj (f i) (g i) ∧ (∀ j : Fin n, j ≠ i → f j = g j))
