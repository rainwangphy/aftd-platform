import AFTD.Prelude

/-!
# binary_partial_word_cube

Topic: combinatorics   Node: 3b8b1097c9ed

Provenance: helper lemma. Reusable finite-cube and ordered-biclique helpers for the uniform OP-205 / RT-1 full-root-gap reduction following arXiv:2610.15635. The deficiency-one singular-coordinate/tree argument formalizes the Boolean setting of arXiv:1103.3693 Lemma 2.5.4 and Corollary 2.5.6; arXiv:2212.14685 Section 2.3 gives a related partition-size discussion. These are helper formalizations, not an original graph covering result; no advance is claimed.

The finite Boolean cube determined by fixing the coordinates of a finite support to the values of a Boolean word.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

def binary_partial_word_cube {V : Type*} [Fintype V] [DecidableEq V]
    (s : Finset V) (b : V → Bool) : Finset (V → Bool) :=
  Fintype.piFinset (fun v => if v ∈ s then {b v} else univ)
