import AFTD.Prelude
import AFTD.Kb.Tcs.Op309LocalNearbyMaskData

/-!
# op309_local_nearby_chunk_0

Topic: combinatorics   Node: 558346dfea1f

Provenance: helper lemma. OP-309 local selection barrier, IN-1099.

The explicit local mask test succeeds on chunk 0 of the finite neighborhood.
-/

theorem op309_local_nearby_chunk_0 : (((In1099Nearby.nearby.drop 0).take 32).all In1099Nearby.check) = true := by decide
