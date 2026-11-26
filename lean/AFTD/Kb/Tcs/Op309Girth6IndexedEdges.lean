import AFTD.Prelude

/-!
# op309_girth6_indexed_edges

Topic: graphs   Node: babebb6bf5a3

Provenance: helper lemma. OP-309 girth-six fixed-P3 obstruction; experiments 41697, 41698 and 41711–41713.

The twenty-four indexed edges of the cubic girth-six base graph.
-/

def op309_girth6_indexed_edges : Fin 24 → Fin 16 × Fin 16 := ![(0,8),(0,9),(0,10),(1,8),(1,11),(1,13),(2,8),(2,12),(2,15),(3,9),(3,11),(3,12),(4,9),(4,13),(4,14),(5,10),(5,12),(5,14),(6,10),(6,13),(6,15),(7,11),(7,14),(7,15)]
