import AFTD.Prelude
import AFTD.Kb.Physics.InstDecidableRelPathGraph

/-!
# dephased_path_marked

Topic: quantum_mechanics   Node: f700b5cd5325

Provenance: formalization of a published result. Source: arXiv:2511.19585, Monogamy of Mutual Information in Graph States

For n : ℕ and S : Finset (Fin n), dephased_path_marked n S is the Finset (Fin n) of vertices u ∈ S for which there exists a vertex v : Fin n not in S whose neighbor finset in SimpleGraph.pathGraph n intersected with S equals {u}.
-/

/-- Marked vertices in S, which are the unique S-neighbors of vertices outside S. -/
def dephased_path_marked (n : ℕ) (S : Finset (Fin n)) : Finset (Fin n) := S.filter fun u => ∃ v : Fin n, v ∉ S ∧ ((SimpleGraph.pathGraph n).neighborFinset v ∩ S = {u})
