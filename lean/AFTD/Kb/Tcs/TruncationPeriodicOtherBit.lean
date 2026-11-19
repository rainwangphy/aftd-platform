import AFTD.Prelude

/-!
# truncation_periodic_other_bit

Topic: graphs   Node: 5c575b54be97

Provenance: helper lemma. Helper for the OP-874 truncation coloring campaign, related to arXiv:2610.41950; finite witnesses are checked in experiments 33310, 33357, 33358 and 33378.

The other bit color in each of the four target residue classes.
-/

def truncation_periodic_other_bit : Fin 4 → Fin 6 := ![1,0,1,0]
