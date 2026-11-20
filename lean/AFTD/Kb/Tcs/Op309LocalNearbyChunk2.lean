import AFTD.Prelude
import AFTD.Kb.Tcs.Op309LocalNearbyMaskData

/-!
# op309_local_nearby_chunk_2

Topic: combinatorics   Node: fcfd9f972c51

Provenance: helper lemma. OP-309 local selection barrier, IN-1099.

The explicit local mask test succeeds on chunk 2 of the finite neighborhood.
-/

theorem op309_local_nearby_chunk_2 : (((In1099Nearby.nearby.drop 64).take 32).all In1099Nearby.check) = true := by decide
