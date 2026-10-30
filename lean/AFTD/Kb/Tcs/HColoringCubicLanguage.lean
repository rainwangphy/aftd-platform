import AFTD.Prelude
import AFTD.Kb.Tcs.EdgeListBoolEncode
import AFTD.Kb.Tcs.EdgeListConnectedCubic
import AFTD.Kb.Tcs.EdgeListHColorable

/-!
# h_coloring_cubic_language

Topic: algorithms   Node: 1b088a2e1f66

Provenance: formalization of a published result. Source: arXiv:2610.35794 (Computational complexity of the H-coloring problem in cubic graphs), Sec. 1-2: the H-coloring problem on cubic graphs (loopless, parallel edges allowed)

For a type W (implicit, W : Type) and H : SimpleGraph W, h_coloring_cubic_language H : Language Bool is the set of Bool words w such that there exist n : ℕ and an edge list es : List (ℕ × ℕ) with w = edge_list_bool_encode es, edge_list_connected_cubic n es, and edge_list_h_colorable H n es.
-/

/-- The H-coloring problem on connected cubic (loopless multi)graphs as a language of Bool words: the unary edge-list encodings `edge_list_bool_encode es` of edge lists `es` on vertices `v < n` that are connected and cubic and admit an H-coloring. -/
def h_coloring_cubic_language {W : Type} (H : SimpleGraph W) : Language Bool :=
  {w | ∃ (n : ℕ) (es : List (ℕ × ℕ)), w = edge_list_bool_encode es ∧
    edge_list_connected_cubic n es ∧ edge_list_h_colorable H n es}
