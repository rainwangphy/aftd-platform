import AFTD.Prelude
import AFTD.Kb.Tcs.IsSpanningPathGraph

/-!
# is_spanning_path_graph_pathGraph_three

Topic: graphs   Node: 3281fa09e867

Provenance: helper lemma. sanity check of is_spanning_path_graph

The path graph on three vertices is a spanning path.
-/

theorem is_spanning_path_graph_pathGraph_three : is_spanning_path_graph (SimpleGraph.pathGraph 3) :=
  ⟨1, fun a b => by simp [SimpleGraph.pathGraph_adj]⟩
