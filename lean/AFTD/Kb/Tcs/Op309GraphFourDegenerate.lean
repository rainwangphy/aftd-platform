import AFTD.Prelude

/-!
# op309_graph_four_degenerate

Topic: graphs   Node: 6d12815733f5

Provenance: helper lemma. Finite greedy-coloring target for the OP-309 path-port route.

Every nonempty finite induced subgraph has a vertex with at most four neighbors in that subgraph.
-/

def op309_graph_four_degenerate {W : Type*} [DecidableEq W]
    (Q : SimpleGraph W) : Prop :=
    ∀ S : Finset W, S.Nonempty → ∃ v ∈ S, ∃ T : Finset W,
      T.card ≤ 4 ∧ ∀ w ∈ S, Q.Adj v w → w ∈ T
