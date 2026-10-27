import AFTD.Prelude

/-!
# binary_partial_word_restrict_support

Topic: combinatorics   Node: b476386dc2d5

Provenance: helper lemma. Reusable finite-cube and ordered-biclique helpers for the uniform OP-205 / RT-1 full-root-gap reduction following arXiv:2610.15635. The deficiency-one singular-coordinate/tree argument formalizes the Boolean setting of arXiv:1103.3693 Lemma 2.5.4 and Corollary 2.5.6; arXiv:2212.14685 Section 2.3 gives a related partition-size discussion. These are helper formalizations, not an original graph covering result; no advance is claimed.

Restrict the support of a partial word to the coordinate subtype excluding one specified coordinate.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

def binary_partial_word_restrict_support {V : Type*} [Fintype V] [DecidableEq V]
    (s : Finset V) (v : V) : Finset {w : V // w ≠ v} :=
  univ.filter (fun w => w.val ∈ s)
