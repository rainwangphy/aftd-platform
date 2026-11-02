import AFTD.Prelude

/-!
# tree_submatrix_ker

Topic: quantum_mechanics   Node: db13180cced8

Provenance: formalization of a published result. Source: Fuentes et al., arXiv:2511.19585; OP-827

For a finite simple graph T on vertex type V and a subset S : Finset V, tree_submatrix_ker T S is the kernel over ZMod 2 of the submatrix of the adjacency matrix of T with row indices in the complement Sᶜ and column indices in S, viewed as a submodule of (↥S → ZMod 2).
-/

/-- Kernel over ZMod 2 of the adjacency submatrix with rows V \ S and columns S. -/
noncomputable def tree_submatrix_ker {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (S : Finset V) :
    Submodule (ZMod 2) (↥S → ZMod 2) := LinearMap.ker (Matrix.toLin' ((T.adjMatrix (ZMod 2)).submatrix
    (fun (r : ↥(Sᶜ : Finset V)) => (r : V)) (fun (c : ↥(S : Finset V)) => (c : V))))
