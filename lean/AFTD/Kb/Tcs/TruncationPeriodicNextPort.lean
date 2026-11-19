import AFTD.Prelude

/-!
# truncation_periodic_next_port

Topic: graphs   Node: 76b4b004bb9c

Provenance: helper lemma. Helper for the OP-874 truncation coloring campaign, related to arXiv:2610.41950; finite witnesses are checked in experiments 33310, 33357, 33358 and 33378.

The periodic high internal colors opposite the following factor ports.
-/

def truncation_periodic_next_port : Fin 4 → Fin 6 := ![4,5,5,3]
