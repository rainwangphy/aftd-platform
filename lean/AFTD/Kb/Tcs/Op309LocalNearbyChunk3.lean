import AFTD.Prelude
import AFTD.Kb.Tcs.Op309LocalNearbyMaskData

/-!
# op309_local_nearby_chunk_3

Topic: combinatorics   Node: bc36cb1ee449

Provenance: helper lemma. OP-309 local selection barrier, IN-1099.

The explicit local mask test succeeds on chunk 3 of the finite neighborhood.
-/

theorem op309_local_nearby_chunk_3 : (((In1099Nearby.nearby.drop 96).take 32).all In1099Nearby.check) = true := by decide
