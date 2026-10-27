import AFTD.Prelude
import AFTD.Kb.Tcs.BinaryPartialWordCube

/-!
# binary_partial_word_cube_mem

Topic: combinatorics   Node: 20b746e364c9

Provenance: helper lemma. Reusable finite-cube and ordered-biclique helpers for the uniform OP-205 / RT-1 full-root-gap reduction following arXiv:2610.15635. The deficiency-one singular-coordinate/tree argument formalizes the Boolean setting of arXiv:1103.3693 Lemma 2.5.4 and Corollary 2.5.6; arXiv:2212.14685 Section 2.3 gives a related partition-size discussion. These are helper formalizations, not an original graph covering result; no advance is claimed.

Membership in a partial-word cube is exactly agreement on every supported coordinate.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem binary_partial_word_cube_mem {V : Type*} [Fintype V] [DecidableEq V]
    (s : Finset V) (b f : V → Bool) :
    f ∈ binary_partial_word_cube s b ↔ ∀ v ∈ s, f v = b v := by
  classical
  simp only [binary_partial_word_cube, Fintype.mem_piFinset]
  constructor
  · intro h v hv
    simpa only [if_pos hv, mem_singleton] using h v
  · intro h v
    by_cases hv : v ∈ s
    · simpa only [if_pos hv, mem_singleton] using h v hv
    · simp only [if_neg hv, mem_univ]
