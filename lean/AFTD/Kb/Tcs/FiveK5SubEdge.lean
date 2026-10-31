import AFTD.Prelude

/-!
# five_k5_sub_edge

Topic: graphs   Node: 3757da77648d

Provenance: helper lemma. step towards degree_list_kempe_diameter_five

K5 on Fin 5 with the single edge {3,4} deleted. Vertices 3 and 4 have degree 3; vertices 0,1,2 have degree 4; the degree sum is 18.
-/

/-- The graph K₅ with the edge {3,4} removed (one of the two 3-connected non-complete graphs on 5 vertices). Declared as an `abbrev` so that `DecidableRel five_k5_sub_edge.Adj` is found by instance search (a plain `def` is not unfolded and `G.degree`, `decide` fail). -/
abbrev five_k5_sub_edge : SimpleGraph (Fin 5) := (⊤ : SimpleGraph (Fin 5)).deleteEdges {Sym2.mk (3 : Fin 5) (4 : Fin 5)}
