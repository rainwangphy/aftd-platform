import AFTD.Prelude

/-!
# truncation_periodic_previous_port

Topic: graphs   Node: 230b89e013fc

Provenance: helper lemma. Helper for the OP-874 truncation coloring campaign, related to arXiv:2610.41950; finite witnesses are checked in experiments 33310, 33357, 33358 and 33378.

The periodic high internal colors opposite the preceding factor ports.
-/

def truncation_periodic_previous_port : Fin 4 → Fin 6 := ![3,4,2,2]
