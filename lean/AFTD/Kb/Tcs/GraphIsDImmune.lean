import AFTD.Prelude
import AFTD.Kb.Tcs.GraphHasDCut

/-!
# graph_is_d_immune

Topic: graphs   Node: 5b7b35097c3e

Provenance: formalization of a published result. Source: arXiv:2611.26556 Section 1

A finite simple graph G is d-immune if it has no d-cut.
-/

/-- A simple graph is d-immune if it has no d-cut. -/
def graph_is_d_immune {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (d : ℕ) : Prop :=
  ¬ graph_has_d_cut G d
