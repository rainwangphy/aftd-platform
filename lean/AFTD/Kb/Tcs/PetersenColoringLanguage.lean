import AFTD.Prelude
import AFTD.Kb.Tcs.EdgeListBoolEncode
import AFTD.Kb.Tcs.EdgeListConnectedCubic
import AFTD.Kb.Tcs.EdgeListHColorable
import AFTD.Kb.Tcs.PetersenGraph

/-!
# petersen_coloring_language

Topic: np_completeness   Node: 75e2216897c7

Provenance: formalization of a published result. Source: arXiv:2610.35794 (Computational complexity of the H-coloring problem in cubic graphs), Sec. 1 and Sec. 4: the H-coloring problem for H = P10 (given a connected cubic graph G, decide whether P10 ≺ G), as the language of encoded YES-instances

The P10-coloring decision problem as a language over Bool (Language Bool): the set of words w such that there exist n : ℕ and es : List (ℕ × ℕ) with w = edge_list_bool_encode es ∧ edge_list_connected_cubic n es ∧ edge_list_h_colorable petersen_graph n es.
-/

/-- Words encoding connected cubic multigraphs that admit a Petersen coloring. -/
def petersen_coloring_language : Language Bool :=
  {w | ∃ (n : ℕ) (es : List (ℕ × ℕ)), w = edge_list_bool_encode es ∧
    edge_list_connected_cubic n es ∧ edge_list_h_colorable petersen_graph n es}
