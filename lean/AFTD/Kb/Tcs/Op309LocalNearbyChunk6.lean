import AFTD.Prelude
import AFTD.Kb.Tcs.Op309LocalNearbyMaskData

/-!
# op309_local_nearby_chunk_6

Topic: combinatorics   Node: 31313cde11b4

Provenance: helper lemma. OP-309 local selection barrier, IN-1099.

The explicit local mask test succeeds on chunk 6 of the finite neighborhood.
-/

theorem op309_local_nearby_chunk_6 : (((In1099Nearby.nearby.drop 192).take 32).all In1099Nearby.check) = true := by decide
