import AFTD.Prelude

/-!
# dephased_path_aux_graph

Topic: quantum_mechanics   Node: 1e0fbf7859b4

Provenance: formalization of a published result. Source: arXiv:2511.19585, Monogamy of Mutual Information in Graph States

For n : ℕ and a finset S : Finset (Fin n), the auxiliary graph dephased_path_aux_graph n S is the SimpleGraph on the subtype S in which two distinct vertices u, w : S are adjacent if and only if there exists a vertex v : Fin n outside S that is adjacent in SimpleGraph.pathGraph n to both u.1 and w.1.
-/

/-- Auxiliary graph on a subset S of a path graph, joining neighbors in S of outside vertices with two neighbors in S. -/
def dephased_path_aux_graph (n : ℕ) (S : Finset (Fin n)) : SimpleGraph S := SimpleGraph.mk (fun u w => u ≠ w ∧ ∃ v : Fin n, v ∉ S ∧ (SimpleGraph.pathGraph n).Adj v u.1 ∧ (SimpleGraph.pathGraph n).Adj v w.1)
