import AFTD.Prelude
import AFTD.Kb.Tcs.Op309LocalNearbyMaskData

/-!
# op309_local_nearby_chunk_7

Topic: combinatorics   Node: 85b88c5f1546

Provenance: helper lemma. OP-309 local selection barrier, IN-1099.

The explicit local mask test succeeds on chunk 7 of the finite neighborhood.
-/

theorem op309_local_nearby_chunk_7 : (((In1099Nearby.nearby.drop 224).take 32).all In1099Nearby.check) = true := by decide
