import AFTD.Prelude
import AFTD.Kb.Tcs.WildJointCanonicalType
import AFTD.Kb.Tcs.WildJointTypeA
import AFTD.Kb.Tcs.WildJointTypeB
import AFTD.Kb.Tcs.WildJointTypeC
import AFTD.Kb.Tcs.WildJointTypeD
import AFTD.Kb.Tcs.WildJointCanonicalMatching

/-!
# wild_joint_canonical_type_values

Topic: graphs   Node: 5703314af948

Provenance: helper lemma. step towards wild_one_bad_color_mixed_moment_formula_with_context

The four concrete triples have canonical orbit types 0,1,2,3 respectively.
-/

open Finset
open scoped BigOperators Classical
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
set_option synthInstance.maxSize 10000

/-- canonical_type of the four representative triples = 0,1,2,3. -/
theorem wild_joint_canonical_type_values (q : ℕ) (hq : 3 ≤ q) : wild_joint_canonical_type q hq (wild_joint_type_A q hq) = 0 ∧ wild_joint_canonical_type q hq (wild_joint_type_B q hq) = 1 ∧ wild_joint_canonical_type q hq (wild_joint_type_C q hq) = 2 ∧ wild_joint_canonical_type q hq (wild_joint_type_D q hq) = 3 := by
  classical
  simp only [wild_joint_canonical_type,wild_joint_type_A,wild_joint_type_B,
    wild_joint_type_C,wild_joint_type_D,exists_mem_insert,mem_singleton,exists_eq_left]
  norm_num [wild_joint_canonical_matching,Fin.ext_iff]
