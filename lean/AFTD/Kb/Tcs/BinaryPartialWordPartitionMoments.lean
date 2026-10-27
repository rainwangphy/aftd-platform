import AFTD.Prelude
import AFTD.Kb.Tcs.BinaryPartialWordCube
import AFTD.Kb.Tcs.BinaryPartialWordCubeMem
import AFTD.Kb.Tcs.BinaryPartialWordCubeDisjoint
import AFTD.Kb.Tcs.BinaryPartialWordSign
import AFTD.Kb.Tcs.BinaryPartialWordCubeSignSum
import AFTD.Kb.Tcs.BinaryPartialWordCubeSignPairSum
import AFTD.Kb.Tcs.BinaryBoolSign

/-!
# binary_partial_word_partition_moments

Topic: combinatorics   Node: a7fa44e4e6f6

Provenance: helper lemma. Reusable finite-cube and ordered-biclique helpers for the uniform OP-205 / RT-1 full-root-gap reduction following arXiv:2610.15635. The deficiency-one singular-coordinate/tree argument formalizes the Boolean setting of arXiv:1103.3693 Lemma 2.5.4 and Corollary 2.5.6; arXiv:2212.14685 Section 2.3 gives a related partition-size discussion. These are helper formalizations, not an original graph covering result; no advance is claimed.

For a partition by pairwise conflicting partial-word cubes, the cardinality-weighted first signed incidences and mixed signed incidences at distinct coordinates all sum to zero.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem binary_partial_word_partition_moments {I V : Type*} [Fintype I] [Fintype V]
    [DecidableEq V] (s : I → Finset V) (b : I → V → Bool)
    (hconflict : ∀ i j, i ≠ j → ∃ v ∈ s i ∩ s j, b i v ≠ b j v)
    (hcover : (univ.biUnion (fun i => binary_partial_word_cube (s i) (b i))) = univ) :
    (∀ v, (∑ i, (binary_partial_word_cube (s i) (b i)).card *
      binary_partial_word_sign (s i) (b i) v) = 0) ∧
    (∀ u v, u ≠ v → (∑ i, (binary_partial_word_cube (s i) (b i)).card *
      binary_partial_word_sign (s i) (b i) u * binary_partial_word_sign (s i) (b i) v) = 0) := by
  classical
  have hdis : (↑(univ : Finset I) : Set I).PairwiseDisjoint
      (fun i => binary_partial_word_cube (s i) (b i)) := by
    intro i hi j hj hij
    exact binary_partial_word_cube_disjoint _ _ _ _ (hconflict i j hij)
  have hempty : binary_partial_word_cube (∅ : Finset V) (fun _ => false) = univ := by
    ext f
    simp [binary_partial_word_cube_mem]
  constructor
  · intro v
    simp_rw [← binary_partial_word_cube_sign_sum]
    rw [← sum_biUnion hdis, hcover]
    have he := binary_partial_word_cube_sign_sum (∅ : Finset V) (fun _ => false) v
    simpa only [hempty, binary_partial_word_sign, Finset.notMem_empty, if_false, mul_zero] using he
  · intro u v huv
    simp_rw [← binary_partial_word_cube_sign_pair_sum _ _ u v huv]
    rw [← sum_biUnion hdis, hcover]
    have he := binary_partial_word_cube_sign_pair_sum (∅ : Finset V) (fun _ => false) u v huv
    simpa only [hempty, binary_partial_word_sign, Finset.notMem_empty, if_false, mul_zero, zero_mul] using he
