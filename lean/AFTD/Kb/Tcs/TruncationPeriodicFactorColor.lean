import AFTD.Prelude

/-!
# truncation_periodic_factor_color

Topic: graphs   Node: fbddb7b85af0

Provenance: helper lemma. Helper for the OP-874 truncation coloring campaign, related to arXiv:2610.41950; finite witnesses are checked in experiments 33310, 33357, 33358 and 33378.

The four periodic high colors of the target factor edges in the forced-path family.
-/

def truncation_periodic_factor_color : Fin 4 → Fin 6 := ![2,3,4,5]
