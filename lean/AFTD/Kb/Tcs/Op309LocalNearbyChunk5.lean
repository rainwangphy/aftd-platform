import AFTD.Prelude
import AFTD.Kb.Tcs.Op309LocalNearbyMaskData

/-!
# op309_local_nearby_chunk_5

Topic: combinatorics   Node: bdc504a0387c

Provenance: helper lemma. OP-309 local selection barrier, IN-1099.

The explicit local mask test succeeds on chunk 5 of the finite neighborhood.
-/

theorem op309_local_nearby_chunk_5 : (((In1099Nearby.nearby.drop 160).take 32).all In1099Nearby.check) = true := by decide
