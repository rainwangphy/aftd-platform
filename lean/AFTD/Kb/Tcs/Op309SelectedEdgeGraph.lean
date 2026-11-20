import AFTD.Prelude

/-!
# op309_selected_edge_graph

Topic: graphs   Node: 093ce1884f93

Provenance: helper lemma. OP-309 overlap-aware port incidence selection, IN-1099.

The spanning graph consisting exactly of the selected edges.
-/

def op309_selected_edge_graph {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (R : Finset G.edgeSet) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (↑(R.image Subtype.val) : Set (Sym2 V))
