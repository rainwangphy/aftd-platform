import AFTD.Prelude
import AFTD.Kb.Tcs.BinaryPartialWordCube

/-!
# binary_partial_word_cube_card

Topic: combinatorics   Node: 640395052e3e

Provenance: helper lemma. Reusable finite-cube and ordered-biclique helpers for the uniform OP-205 / RT-1 full-root-gap reduction following arXiv:2610.15635. The deficiency-one singular-coordinate/tree argument formalizes the Boolean setting of arXiv:1103.3693 Lemma 2.5.4 and Corollary 2.5.6; arXiv:2212.14685 Section 2.3 gives a related partition-size discussion. These are helper formalizations, not an original graph covering result; no advance is claimed.

A partial-word cube on a finite coordinate type has cardinality two to the number of coordinates outside its support.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem binary_partial_word_cube_card {V : Type*} [Fintype V] [DecidableEq V]
    (s : Finset V) (b : V → Bool) :
    (binary_partial_word_cube s b).card = 2 ^ (Fintype.card V - s.card) := by
  classical
  rw [binary_partial_word_cube, Fintype.card_piFinset]
  simp_rw [apply_ite Finset.card, card_singleton, card_univ, Fintype.card_bool]
  rw [prod_ite]
  simp only [prod_const_one, one_mul, prod_const]
  congr 1
  simpa only [filter_not, filter_mem_eq_inter, univ_inter, card_univ] using
    (card_sdiff_of_subset (subset_univ s))
