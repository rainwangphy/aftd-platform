import AFTD.Prelude
import AFTD.Kb.Tcs.Op309LocalNearbyMaskData

/-!
# op309_local_nearby_chunk_11

Topic: combinatorics   Node: 81bd6c9430ea

Provenance: helper lemma. OP-309 local selection barrier, IN-1099.

The explicit local mask test succeeds on chunk 11 of the finite neighborhood.
-/

theorem op309_local_nearby_chunk_11 : (((In1099Nearby.nearby.drop 352).take 32).all In1099Nearby.check) = true := by decide
