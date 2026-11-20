import AFTD.Prelude
import AFTD.Kb.Tcs.Op309LocalNearbyMaskData

/-!
# op309_local_nearby_chunk_9

Topic: combinatorics   Node: 6075fedcdb9a

Provenance: helper lemma. OP-309 local selection barrier, IN-1099.

The explicit local mask test succeeds on chunk 9 of the finite neighborhood.
-/

theorem op309_local_nearby_chunk_9 : (((In1099Nearby.nearby.drop 288).take 32).all In1099Nearby.check) = true := by decide
