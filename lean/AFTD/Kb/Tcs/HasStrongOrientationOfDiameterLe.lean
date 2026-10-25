import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphReachWithin
import AFTD.Kb.Tcs.IsGraphOrientation

/-!
# has_strong_orientation_of_diameter_le

Topic: graphs   Node: db0c84548b6c

Provenance: formalization of a published result. Source: arXiv:2610.09648 (An asymptotically tight bound on oriented diameter), Section 1: strong orientation and directed diameter; the oriented diameter is the minimum directed diameter over strong orientations.

The simple graph G has an orientation D (each edge of G gets exactly one direction, no other arcs) in which every ordered pair of vertices u, v is joined by a directed walk of length at most k; i.e. G has a strong orientation of directed diameter at most k (oriented diameter of G is at most k).
-/

def has_strong_orientation_of_diameter_le {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ D : Digraph V, is_graph_orientation G D ∧ ∀ u v, digraph_reach_within D k u v
