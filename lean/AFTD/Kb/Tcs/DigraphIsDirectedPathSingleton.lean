import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphIsDirectedPath

/-!
# digraph_is_directed_path_singleton

Topic: graphs   Node: 73192685491b

Provenance: helper lemma. folklore

For every digraph D and vertex v, the singleton list [v] is a directed path from v to v.
-/

/-- The singleton list [v] is a directed path from v to v in any digraph. -/
theorem digraph_is_directed_path_singleton {V : Type*} (D : Digraph V) (v : V) :
    digraph_is_directed_path D [v] v v := by
  simp [digraph_is_directed_path]
