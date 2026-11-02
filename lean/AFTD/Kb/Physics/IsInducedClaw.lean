import AFTD.Prelude

/-!
# is_induced_claw

Topic: quantum_mechanics   Node: b76f366da94e

Provenance: formalization of a published result. Source: arXiv:2511.19585

For a simple graph G on type V and a finite subset of vertices s : Finset V, is_induced_claw G s asserts that the induced subgraph of G on s is isomorphic to the complete bipartite graph completeBipartiteGraph (Fin 1) (Fin 3).
-/

/-- A subset of four vertices inducing the complete bipartite graph K_{1,3} (a claw). -/
def is_induced_claw {V : Type*} (G : SimpleGraph V) (s : Finset V) : Prop := Nonempty (G.induce (s : Set V) ≃g completeBipartiteGraph (Fin 1) (Fin 3))
