import AFTD.Prelude
import AFTD.Kb.Tcs.WildJointEvenCanonicalOrbitObstruction
import AFTD.Kb.Tcs.WildJointAlpha
import AFTD.Kb.Tcs.WildJointCanonicalType

/-!
# not_wild_joint_alpha_type_well_defined

Topic: graphs   Node: 12a0f35344b3

Provenance: helper lemma. IN-382 / OP-306 campaign9, 2026-10-30. Standard finite matching symmetry supporting the mixed-moment route for https://arxiv.org/html/2610.22142v1. Exact experiment9566 exposed the missing parity assumption. The original false helper remains retired and its proof record is preserved. No wild-number bound or research advance is claimed.

The stored universal assertion wild_joint_alpha_type_well_defined is false. Its exact logical negation follows at q=4 from equal declared types for{1,2,11} and{1,2,3} with unequal alpha. This is an internal helper correction, not a paper erratum or a refutation of OP-306.
-/

open Finset
open scoped BigOperators Classical
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 10000

theorem not_wild_joint_alpha_type_well_defined : ¬ (∀ (q : ℕ) (hq : 3 ≤ q) (T T' : Finset (Fin (3*q))) (hT : T.card = 3) (hT' : T'.card = 3) (hty : wild_joint_canonical_type q hq T = wild_joint_canonical_type q hq T'), wild_joint_alpha q T = wild_joint_alpha q T') := by
  intro h
  have ho := wild_joint_even_canonical_orbit_obstruction
  have he := h 4 (by omega) {1,2,11} {1,2,3}
    (by norm_num [Fin.ext_iff]) (by norm_num [Fin.ext_iff]) ho.1
  have hh := ho.2.2
  rw [← he,ho.2.1] at hh
  exact lt_irrefl _ hh
