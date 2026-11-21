import AFTD.Prelude
import AFTD.Kb.Tcs.GraphIsDCut

/-!
# graph_has_d_cut

Topic: graphs   Node: abb17c0fe21a

Provenance: formalization of a published result. Source: arXiv:2611.26556 Section 1

A finite simple graph G has a d-cut if there exists a subset A of vertices forming a d-cut.
-/

/-- A simple graph has a d-cut if there exists a d-cut partition of its vertices. -/
def graph_has_d_cut {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∃ A : Finset V, graph_is_d_cut G d A
