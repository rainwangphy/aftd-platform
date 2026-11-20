import AFTD.Prelude
import AFTD.Kb.Tcs.Op309LocalNearbyMaskData

/-!
# op309_local_nearby_chunk_10

Topic: combinatorics   Node: c6ddf7de1fcc

Provenance: helper lemma. OP-309 local selection barrier, IN-1099.

The explicit local mask test succeeds on chunk 10 of the finite neighborhood.
-/

theorem op309_local_nearby_chunk_10 : (((In1099Nearby.nearby.drop 320).take 32).all In1099Nearby.check) = true := by decide
