import AFTD.Prelude

/-!
# sym2_edge_degree

Topic: graphs   Node: 1cc79bcf9419

Provenance: helper lemma. step towards simple_graph_stable_packing_unforced_conflict_odd_cycle

The number of edges of a finite edge set F that are incident to a vertex v.
-/

/-- `sym2_edge_degree F v` is the number of edges in the edge set `F` incident to `v` (counting an edge once for each of its endpoints; `v ∈ e` is `Sym2.Mem`). -/
def sym2_edge_degree {V : Type*} [DecidableEq V] (F : Finset (Sym2 V)) (v : V) : ℕ := (F.filter (fun e => v ∈ e)).card
