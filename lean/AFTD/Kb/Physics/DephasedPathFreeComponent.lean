import AFTD.Prelude
import AFTD.Kb.Physics.DephasedPathAuxGraph
import AFTD.Kb.Physics.DephasedPathMarked

/-!
# dephased_path_free_component

Topic: quantum_mechanics   Node: f2b100fc6648

Provenance: formalization of a published result. Source: arXiv:2511.19585, Monogamy of Mutual Information in Graph States

For n : ℕ and S : Finset (Fin n), a connected component c of dephased_path_aux_graph n S is free if every vertex u : S in the component satisfies u.1 ∉ dephased_path_marked n S.
-/

/-- Predicate that a connected component of the auxiliary graph contains no marked vertex. -/
def dephased_path_free_component (n : ℕ) (S : Finset (Fin n)) (c : (dephased_path_aux_graph n S).ConnectedComponent) : Prop := ∀ u : S, (dephased_path_aux_graph n S).connectedComponentMk u = c → u.1 ∉ dephased_path_marked n S
