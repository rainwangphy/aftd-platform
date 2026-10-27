import AFTD.Prelude
import AFTD.Kb.Tcs.BinaryBoolSign

/-!
# binary_partial_word_sign

Topic: combinatorics   Node: d4d07cc8be05

Provenance: helper lemma. Reusable finite-cube and ordered-biclique helpers for the uniform OP-205 / RT-1 full-root-gap reduction following arXiv:2610.15635. The deficiency-one singular-coordinate/tree argument formalizes the Boolean setting of arXiv:1103.3693 Lemma 2.5.4 and Corollary 2.5.6; arXiv:2212.14685 Section 2.3 gives a related partition-size discussion. These are helper formalizations, not an original graph covering result; no advance is claimed.

The rational signed incidence of a coordinate in a partial word, with zero outside its support.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

def binary_partial_word_sign {V : Type*} [DecidableEq V]
    (s : Finset V) (b : V → Bool) (v : V) : ℚ :=
  if v ∈ s then binary_bool_sign (b v) else 0
