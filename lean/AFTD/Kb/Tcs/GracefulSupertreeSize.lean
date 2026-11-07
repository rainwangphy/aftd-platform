import AFTD.Prelude
import AFTD.Kb.Tcs.IsGracefulTree

/-!
# graceful_supertree_size

Topic: graphs   Node: 3c8b25029d5f

Provenance: formalization of a published result. Source: arXiv:2611.01340 Section 1

For a finite simple graph T, the graceful supertree size of T is the minimum number of edges M of a graceful tree on vertex set Fin (M + 1) containing T as an induced subgraph (or 0 if no such graceful tree exists).
-/

/-- The minimum number of edges s(T) of a graceful tree containing T as a subtree. -/
noncomputable def graceful_supertree_size {V : Type*} [Fintype V] (T : SimpleGraph V) : ℕ := sInf {M : ℕ | ∃ G : SimpleGraph (Fin (M + 1)),
    is_graceful_tree G ∧ Nonempty (SimpleGraph.Embedding T G)}
