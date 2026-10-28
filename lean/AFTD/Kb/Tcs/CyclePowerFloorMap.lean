import AFTD.Prelude

/-!
# cycle_power_floor_map

Topic: combinatorics   Node: 566faa22ef07

Provenance: helper lemma. arXiv:2610.15635, Proposition 3.2, with induced floor embedding from Lemma 3.1 and cover restriction from Lemma 2.1. This formalizes the published upper bound serving OP-205 / RT-1; no new research result is claimed.

The map from ZMod n to ZMod N sending a vertex u to the residue class of floor(u.val*N/n).
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

def cycle_power_floor_map (n N : ℕ) (u : ZMod n) : ZMod N := ((u.val*N/n : ℕ) : ZMod N)
