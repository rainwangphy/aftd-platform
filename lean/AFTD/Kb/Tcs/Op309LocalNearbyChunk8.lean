import AFTD.Prelude
import AFTD.Kb.Tcs.Op309LocalNearbyMaskData

/-!
# op309_local_nearby_chunk_8

Topic: combinatorics   Node: 97c4fd509f63

Provenance: helper lemma. OP-309 local selection barrier, IN-1099.

The explicit local mask test succeeds on chunk 8 of the finite neighborhood.
-/

theorem op309_local_nearby_chunk_8 : (((In1099Nearby.nearby.drop 256).take 32).all In1099Nearby.check) = true := by decide
