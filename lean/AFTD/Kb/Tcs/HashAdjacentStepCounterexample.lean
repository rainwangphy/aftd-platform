import AFTD.Prelude
import AFTD.Kb.Tcs.HashAdjacentCount
import AFTD.Kb.Tcs.HashInsertStep
import AFTD.Kb.Tcs.LinearProbeOffset

/-!
# hash_adjacent_step_counterexample

Topic: data_structures   Node: e254b8972b42

Provenance: helper lemma. Unit-first fixed-offset mean-probe extremality; experiments 11670–11680 and arXiv:2610.31363.

On a fixed occupied set, a unit-first order can create more adjacent pairs on average in the next step than linear probing.
-/

theorem hash_adjacent_step_counterexample :
  (∑ h : ZMod 6, hash_adjacent_count 6 1
    (hash_insert_step 6 ![(0 : ZMod 6),1,4,5,2,3] ({0,2,3} : Finset (ZMod 6)) h)) = 15 ∧
  (∑ h : ZMod 6, hash_adjacent_count 6 1
    (hash_insert_step 6 (linear_probe_offset 6) ({0,2,3} : Finset (ZMod 6)) h)) = 14 := by decide +kernel
