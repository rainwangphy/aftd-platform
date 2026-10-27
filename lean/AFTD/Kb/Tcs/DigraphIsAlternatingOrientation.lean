import AFTD.Prelude
import AFTD.Kb.Tcs.IsGraphOrientation

/-!
# digraph_is_alternating_orientation

Topic: graphs   Node: 537802d2547f

Provenance: formalization of a published result. Source: arXiv:2610.25886 (Extremal arborescences in graph orientations), Sec. 1 and Thm 1.1 (alternating orientations of plane Eulerian graphs)

For a simple graph G, a permutation σ : Equiv.Perm G.Dart of the darts of G (in use, a rotation system: the cyclic order of darts around each vertex) and a digraph D on the same vertex type, D is an alternating orientation for σ: is_graph_orientation G D holds, and for every dart d = (u, w) of G, D has the arc u → w iff D does not have the arc along the dart σ d, so consecutive darts around each vertex point opposite ways and incoming and outgoing arcs alternate.
-/

/-- D is alternating for σ: at each vertex, consecutive darts in the rotation have opposite directions. -/
def digraph_is_alternating_orientation {V : Type*} (G : SimpleGraph V) (σ : Equiv.Perm G.Dart)
    (D : Digraph V) : Prop :=
  is_graph_orientation G D ∧ ∀ d : G.Dart, (D.Adj d.fst d.snd ↔ ¬ D.Adj (σ d).fst (σ d).snd)
