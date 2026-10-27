import AFTD.Prelude
import AFTD.Kb.Tcs.IsGraphOrientation

/-!
# digraph_is_eulerian_orientation

Topic: graphs   Node: d7beda5343d4

Provenance: formalization of a published result. Source: arXiv:2610.25886 (Extremal arborescences in graph orientations), Sec. 1 (Eulerian orientations)

For a simple graph G and a digraph D on the vertex type Fin n (as for digraph_arborescence_count_at), D is an Eulerian orientation of G: is_graph_orientation G D holds, and at every vertex v the out-degree #{w | D.Adj v w} equals the in-degree #{w | D.Adj w v}, both counted with Finset.univ.filter.
-/

/-- D is an Eulerian orientation of G: in-degree equals out-degree at every vertex. -/
def digraph_is_eulerian_orientation {n : ℕ} (G : SimpleGraph (Fin n)) (D : Digraph (Fin n))
    [DecidableRel D.Adj] : Prop :=
  is_graph_orientation G D ∧
    ∀ v, (Finset.univ.filter (fun w => D.Adj v w)).card = (Finset.univ.filter (fun w => D.Adj w v)).card
