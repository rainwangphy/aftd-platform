import AFTD.Prelude
import AFTD.Kb.Tcs.BinaryPartialWordCube
import AFTD.Kb.Tcs.BinaryPartialWordCubeMem
import AFTD.Kb.Tcs.BinaryBoolSign
import AFTD.Kb.Tcs.BinaryBoolSignNot
import AFTD.Kb.Tcs.BinaryPartialWordSign
import AFTD.Kb.Tcs.BinaryPartialWordCubeOddSum

/-!
# binary_partial_word_cube_sign_pair_sum

Topic: combinatorics   Node: a4c8fbc8baaa

Provenance: helper lemma. Reusable finite-cube and ordered-biclique helpers for the uniform OP-205 / RT-1 full-root-gap reduction following arXiv:2610.15635. The deficiency-one singular-coordinate/tree argument formalizes the Boolean setting of arXiv:1103.3693 Lemma 2.5.4 and Corollary 2.5.6; arXiv:2212.14685 Section 2.3 gives a related partition-size discussion. These are helper formalizations, not an original graph covering result; no advance is claimed.

For distinct coordinates, their sign product summed on a partial-word cube equals its cardinality times the two signed incidences.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem binary_partial_word_cube_sign_pair_sum {V : Type*} [Fintype V] [DecidableEq V]
    (s : Finset V) (b : V → Bool) (u v : V) (huv : u ≠ v) :
    (∑ f ∈ binary_partial_word_cube s b, binary_bool_sign (f u) * binary_bool_sign (f v)) =
      (binary_partial_word_cube s b).card * binary_partial_word_sign s b u *
        binary_partial_word_sign s b v := by
  classical
  by_cases hu : u ∈ s
  · by_cases hv : v ∈ s
    · simp only [binary_partial_word_sign, if_pos hu, if_pos hv]
      calc
        _ = ∑ f ∈ binary_partial_word_cube s b,
            binary_bool_sign (b u) * binary_bool_sign (b v) := by
          apply sum_congr rfl
          intro f hf
          rw [(binary_partial_word_cube_mem s b f).mp hf u hu,
            (binary_partial_word_cube_mem s b f).mp hf v hv]
        _ = _ := by simp [mul_assoc]
    · simp only [binary_partial_word_sign, if_pos hu, if_neg hv, mul_zero]
      apply binary_partial_word_cube_odd_sum s b v hv
      intro f hf
      simp only [Function.update_of_ne huv, Function.update_self, binary_bool_sign_not]
      ring
  · simp only [binary_partial_word_sign, if_neg hu, mul_zero, zero_mul]
    apply binary_partial_word_cube_odd_sum s b u hu
    intro f hf
    simp only [Function.update_self, Function.update_of_ne huv.symm, binary_bool_sign_not]
    ring
