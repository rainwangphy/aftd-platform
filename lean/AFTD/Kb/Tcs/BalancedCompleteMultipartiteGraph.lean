import AFTD.Prelude

/-!
# balanced_complete_multipartite_graph

Topic: graphs   Node: 8f97f647fa37

Provenance: formalization of a published result. Source: arXiv:2610.18636 (spectral distances; nearest spectra to complete multipartite graphs): the complete multipartite graph K_{n,...,n}

For natural numbers r and n, balanced_complete_multipartite_graph r n is the simple graph on Fin (r * n) in which u and v are adjacent exactly when u / n ≠ v / n (natural-number division of the vertex values): the complete r-partite graph T_{r,n} = K_{n,...,n} whose parts are the blocks {kn, ..., kn + n - 1}, k < r.
-/

def balanced_complete_multipartite_graph (r n : ℕ) : SimpleGraph (Fin (r * n)) := { Adj := fun u v => (u : ℕ) / n ≠ (v : ℕ) / n, symm := ⟨fun _ _ h => Ne.symm h⟩, loopless := ⟨fun _ h => h rfl⟩ }
