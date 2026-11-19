import AFTD.Prelude

/-!
# truncation_periodic_auxiliary_exposure

Topic: graphs   Node: 27da6210f306

Provenance: helper lemma. Helper for the OP-874 truncation coloring campaign, related to arXiv:2610.41950; finite witnesses are checked in experiments 33310, 33357, 33358 and 33378.

The periodic high colors exposed by the matching ports in the auxiliary blocks.
-/

def truncation_periodic_auxiliary_exposure : Fin 4 → Fin 6 := ![2,2,4,4]
