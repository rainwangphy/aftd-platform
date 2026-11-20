import AFTD.Prelude
import AFTD.Kb.Tcs.Op309LocalNearbyMaskData

/-!
# op309_local_nearby_chunk_4

Topic: combinatorics   Node: cfd009a1e830

Provenance: helper lemma. OP-309 local selection barrier, IN-1099.

The explicit local mask test succeeds on chunk 4 of the finite neighborhood.
-/

theorem op309_local_nearby_chunk_4 : (((In1099Nearby.nearby.drop 128).take 32).all In1099Nearby.check) = true := by decide
