import AFTD.Prelude

/-!
# op309_girth5_twenty_indexed_edges

Topic: graphs   Node: 2be3aeaa855a

Provenance: helper lemma. OP-309; girth-five global port-consistency obstruction and cyclic covers, experiments 41769, 41785–41788, 41792–41797.

The thirty indexed edges of the twenty-vertex girth-five stress graph.
-/

def op309_girth5_twenty_indexed_edges : Fin 30 → Fin 20 × Fin 20 := ![(0,7),(0,9),(0,15),(1,6),(1,8),(1,14),(2,11),(2,14),(2,16),(3,4),(3,8),(3,19),(4,6),(4,18),(5,8),(5,10),(5,13),(6,13),(7,14),(7,18),(9,10),(9,17),(10,16),(11,12),(11,17),(12,13),(12,15),(15,19),(16,18),(17,19)]
