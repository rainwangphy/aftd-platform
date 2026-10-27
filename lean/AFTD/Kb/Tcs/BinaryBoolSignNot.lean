import AFTD.Prelude
import AFTD.Kb.Tcs.BinaryBoolSign

/-!
# binary_bool_sign_not

Topic: combinatorics   Node: 38e9880cfd29

Provenance: helper lemma. Reusable finite-cube and ordered-biclique helpers for the uniform OP-205 / RT-1 full-root-gap reduction following arXiv:2610.15635. The deficiency-one singular-coordinate/tree argument formalizes the Boolean setting of arXiv:1103.3693 Lemma 2.5.4 and Corollary 2.5.6; arXiv:2212.14685 Section 2.3 gives a related partition-size discussion. These are helper formalizations, not an original graph covering result; no advance is claimed.

Negating a Boolean value negates its rational sign.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem binary_bool_sign_not (b : Bool) :
    binary_bool_sign (!b) = -binary_bool_sign b := by
  cases b <;> norm_num [binary_bool_sign]
