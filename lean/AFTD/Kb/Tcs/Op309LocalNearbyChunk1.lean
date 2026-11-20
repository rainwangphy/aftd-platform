import AFTD.Prelude
import AFTD.Kb.Tcs.Op309LocalNearbyMaskData

/-!
# op309_local_nearby_chunk_1

Topic: combinatorics   Node: 3f5238cacaaa

Provenance: helper lemma. OP-309 local selection barrier, IN-1099.

The explicit local mask test succeeds on chunk 1 of the finite neighborhood.
-/

theorem op309_local_nearby_chunk_1 : (((In1099Nearby.nearby.drop 32).take 32).all In1099Nearby.check) = true := by decide
