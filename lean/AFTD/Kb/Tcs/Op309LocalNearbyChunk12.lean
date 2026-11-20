import AFTD.Prelude
import AFTD.Kb.Tcs.Op309LocalNearbyMaskData

/-!
# op309_local_nearby_chunk_12

Topic: combinatorics   Node: 1b8fa10c2e61

Provenance: helper lemma. OP-309 local selection barrier, IN-1099.

The explicit local mask test succeeds on chunk 12 of the finite neighborhood.
-/

theorem op309_local_nearby_chunk_12 : (((In1099Nearby.nearby.drop 384).take 32).all In1099Nearby.check) = true := by decide
