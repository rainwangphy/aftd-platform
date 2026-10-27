import AFTD.Prelude
import AFTD.Kb.Tcs.BinaryPartialWordCube
import AFTD.Kb.Tcs.BinaryPartialWordCubeCard
import AFTD.Kb.Tcs.BinaryPartialWordCubeDisjoint

/-!
# binary_partial_word_cube_packing

Topic: combinatorics   Node: c408070d2662

Provenance: helper lemma. Reusable finite-cube and ordered-biclique helpers for the uniform OP-205 / RT-1 full-root-gap reduction following arXiv:2610.15635. The deficiency-one singular-coordinate/tree argument formalizes the Boolean setting of arXiv:1103.3693 Lemma 2.5.4 and Corollary 2.5.6; arXiv:2212.14685 Section 2.3 gives a related partition-size discussion. These are helper formalizations, not an original graph covering result; no advance is claimed.

Pairwise conflicting partial words pack disjoint cubes into the full Boolean cube, bounding the sum of their cardinalities.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem binary_partial_word_cube_packing {I V : Type*} [Fintype I] [Fintype V]
    [DecidableEq V] (s : I → Finset V) (b : I → V → Bool)
    (hconflict : ∀ i j, i ≠ j → ∃ v ∈ s i ∩ s j, b i v ≠ b j v) :
    ∑ i, (2 : ℚ) ^ (Fintype.card V - (s i).card) ≤ 2 ^ Fintype.card V := by
  classical
  have hdis : (↑(univ : Finset I) : Set I).PairwiseDisjoint
      (fun i => binary_partial_word_cube (s i) (b i)) := by
    intro i hi j hj hij
    exact binary_partial_word_cube_disjoint _ _ _ _ (hconflict i j hij)
  have hc := Finset.card_le_card
    (show (univ.biUnion (fun i => binary_partial_word_cube (s i) (b i))) ⊆ univ from
      subset_univ _)
  rw [Finset.card_biUnion hdis] at hc
  simp only [binary_partial_word_cube_card, card_univ, Fintype.card_fun, Fintype.card_bool] at hc
  exact_mod_cast hc
