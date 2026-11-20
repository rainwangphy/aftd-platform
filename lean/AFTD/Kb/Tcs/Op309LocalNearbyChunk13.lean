import AFTD.Prelude
import AFTD.Kb.Tcs.Op309LocalNearbyMaskData

/-!
# op309_local_nearby_chunk_13

Topic: combinatorics   Node: 36d661b53b0a

Provenance: helper lemma. OP-309 local selection barrier, IN-1099.

The explicit local mask test succeeds on chunk 13 of the finite neighborhood.
-/

theorem op309_local_nearby_chunk_13 : (((In1099Nearby.nearby.drop 416).take 32).all In1099Nearby.check) = true := by decide
