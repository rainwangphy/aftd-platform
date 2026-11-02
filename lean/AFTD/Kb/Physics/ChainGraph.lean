import AFTD.Prelude

/-!
# chain_graph

Topic: quantum_mechanics   Node: 4348a24ef374

Provenance: formalization of a published result. Source: knowledgebase: OP-828

Given a graph G on Fin m and a marked vertex v0, chain_graph G v0 k is the graph on Fin k × Fin m formed by k copies of G connected linearly by edges between consecutive copies at v0.
-/

/-- Chain of k copies of a marked finite simple graph connected at the marked vertex. -/
def chain_graph {m : ℕ} (G : SimpleGraph (Fin m)) (v0 : Fin m) (k : ℕ) :
    SimpleGraph (Fin k × Fin m) := SimpleGraph.fromRel (fun u v =>
    (u.1 = v.1 ∧ G.Adj u.2 v.2) ∨
    (u.2 = v0 ∧ v.2 = v0 ∧ (u.1.val + 1 = v.1.val ∨ v.1.val + 1 = u.1.val)))
