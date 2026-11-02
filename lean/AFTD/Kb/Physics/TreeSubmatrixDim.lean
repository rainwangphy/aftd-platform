import AFTD.Prelude
import AFTD.Kb.Physics.TreeSubmatrixKer

/-!
# tree_submatrix_dim

Topic: quantum_mechanics   Node: 643676295234

Provenance: formalization of a published result. Source: Fuentes et al., arXiv:2511.19585; OP-827

For a finite simple graph T on vertex type V and a subset S : Finset V, tree_submatrix_dim T S is the dimension (finrank) over ZMod 2 of the kernel tree_submatrix_ker T S.
-/

/-- Dimension over ZMod 2 of the kernel of the adjacency submatrix for S. -/
noncomputable def tree_submatrix_dim {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (S : Finset V) : ℕ := Module.finrank (ZMod 2) (tree_submatrix_ker T S)
