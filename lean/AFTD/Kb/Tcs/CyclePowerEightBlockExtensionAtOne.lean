import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerEightBlockExtensionAt

/-!
# cycle_power_eight_block_extension_at_one

Topic: combinatorics   Node: 636cf0389b56

Provenance: helper lemma. Uniform local structural route for OP-205 / RT-1, following arXiv:2610.15635. The Boolean eight-block extension remains conjectured; the induction result keeps it as an explicit hypothesis. Finite guarded computations are evidence only, and no graph covering value or research advance is claimed.

The eight-block extension predicate holds at block size one.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem cycle_power_eight_block_extension_at_one :
    cycle_power_eight_block_extension_at 1 := by
  intro x he _ _ _ _ _ p
  constructor
  · intro a b hab hb hx
    by_cases ha : a=0
    · subst a; exact (he p).1
    · have h : a=b := by omega
      rwa [h]
  · intro a b ha hab hb hx
    by_cases hlast : b=7
    · subst b
      simpa using (he p).2
    · have h : a=b := by omega
      rwa [← h]
