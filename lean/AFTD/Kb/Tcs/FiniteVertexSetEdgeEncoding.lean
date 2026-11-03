import AFTD.Prelude

/-!
# finite_vertex_set_edge_encoding

Topic: graphs   Node: 095e35478f06

Provenance: helper lemma. Bridge from vertex-triangle packings to point-set families for the separator route.

The non-diagonal unordered vertex pairs spanned by a finite vertex set.
-/

def finite_vertex_set_edge_encoding {V : Type*} [DecidableEq V] (s : Finset V) : Finset (Sym2 V) := s.sym2.filter (fun e => ¬ e.IsDiag)
