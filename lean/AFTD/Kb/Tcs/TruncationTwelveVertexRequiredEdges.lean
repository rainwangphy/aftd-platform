import AFTD.Prelude

/-!
# truncation_twelve_vertex_required_edges

Topic: graphs   Node: 21cb3a5cd981

Provenance: helper lemma. Helper for the OP-874 truncation coloring campaign; the concrete instance is independently checked in experiments 33309, 33310, 33320, 33321 and 33322.

The twelve explicitly listed mandatory edges in the finite cubic instance underlying the path-window obstruction.
-/

def truncation_twelve_vertex_required_edges : Finset (Sym2 (Fin 12)) :=
  {s(0, 5), s(0, 10), s(1, 2), s(1, 4), s(2, 3), s(2, 7),
   s(3, 4), s(3, 9), s(5, 6), s(6, 11), s(8, 11), s(10, 11)}
