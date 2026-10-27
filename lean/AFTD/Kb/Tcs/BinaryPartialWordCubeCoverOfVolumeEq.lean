import AFTD.Prelude
import AFTD.Kb.Tcs.BinaryPartialWordCube
import AFTD.Kb.Tcs.BinaryPartialWordCubeCard
import AFTD.Kb.Tcs.BinaryPartialWordCubeDisjoint

/-!
# binary_partial_word_cube_cover_of_volume_eq

Topic: combinatorics   Node: e516c3629379

Provenance: helper lemma. Reusable finite-cube and ordered-biclique helpers for the uniform OP-205 / RT-1 full-root-gap reduction following arXiv:2610.15635. The deficiency-one singular-coordinate/tree argument formalizes the Boolean setting of arXiv:1103.3693 Lemma 2.5.4 and Corollary 2.5.6; arXiv:2212.14685 Section 2.3 gives a related partition-size discussion. These are helper formalizations, not an original graph covering result; no advance is claimed.

Pairwise conflicting partial words whose rational volume sum is one cover the entire finite Boolean cube.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem binary_partial_word_cube_cover_of_volume_eq {I V : Type*} [Fintype I] [Fintype V]
    [DecidableEq V] (s : I → Finset V) (b : I → V → Bool)
    (hconflict : ∀ i j, i ≠ j → ∃ v ∈ s i ∩ s j, b i v ≠ b j v)
    (hvolume : (∑ i, (1 : ℚ) / 2^(s i).card) = 1) :
    (univ.biUnion (fun i => binary_partial_word_cube (s i) (b i))) = univ := by
  classical
  have hdis : (↑(univ : Finset I) : Set I).PairwiseDisjoint
      (fun i => binary_partial_word_cube (s i) (b i)) := by
    intro i hi j hj hij
    exact binary_partial_word_cube_disjoint _ _ _ _ (hconflict i j hij)
  apply eq_univ_of_card
  rw [card_biUnion hdis]
  simp only [binary_partial_word_cube_card, Fintype.card_fun, Fintype.card_bool]
  have he (i : I) : (2 : ℚ) ^ (Fintype.card V - (s i).card) =
      2 ^ Fintype.card V * (1 / 2 ^ (s i).card) := by
    rw [pow_sub₀ _ (by norm_num) (card_le_univ _)]
    simp only [one_div]
  have hq : (∑ i, (2 : ℚ)^(Fintype.card V - (s i).card)) = 2^Fintype.card V := by
    simp_rw [he]
    rw [← mul_sum, hvolume, mul_one]
  exact_mod_cast hq
