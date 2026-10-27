import AFTD.Prelude
import AFTD.Kb.Tcs.BinaryPartialWordCube
import AFTD.Kb.Tcs.BinaryPartialWordCubeCard
import AFTD.Kb.Tcs.BinaryBoolSign
import AFTD.Kb.Tcs.BinaryPartialWordSign
import AFTD.Kb.Tcs.BinaryPartialWordPartitionMoments
import AFTD.Kb.Tcs.WeightedOrthogonalCardBound

/-!
# binary_partial_word_partition_dimension_bound

Topic: combinatorics   Node: 4559ead84df5

Provenance: helper lemma. Reusable finite-cube and ordered-biclique helpers for the uniform OP-205 / RT-1 full-root-gap reduction following arXiv:2610.15635. The deficiency-one singular-coordinate/tree argument formalizes the Boolean setting of arXiv:1103.3693 Lemma 2.5.4 and Corollary 2.5.6; arXiv:2212.14685 Section 2.3 gives a related partition-size discussion. These are helper formalizations, not an original graph covering result; no advance is claimed.

A finite partition of a Boolean cube by pairwise conflicting partial words, mentioning every coordinate, has at least one more part than coordinates.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem binary_partial_word_partition_dimension_bound {I V : Type*} [Fintype I] [Fintype V]
    [DecidableEq V] (s : I → Finset V) (b : I → V → Bool)
    (hconflict : ∀ i j, i ≠ j → ∃ v ∈ s i ∩ s j, b i v ≠ b j v)
    (hcover : (univ.biUnion (fun i => binary_partial_word_cube (s i) (b i))) = univ)
    (hessential : ∀ v, ∃ i, v ∈ s i) :
    Fintype.card V + 1 ≤ Fintype.card I := by
  classical
  let w : I → ℚ := fun i => (binary_partial_word_cube (s i) (b i)).card
  let y : Option V → I → ℚ := fun a i =>
    match a with
    | none => 1
    | some v => binary_partial_word_sign (s i) (b i) v
  have hw (i : I) : 0 < w i := by
    dsimp [w]
    rw [binary_partial_word_cube_card]
    positivity
  have hex : ∃ i : I, True := by
    have hf : (fun _ : V => false) ∈
        univ.biUnion (fun i => binary_partial_word_cube (s i) (b i)) := by
      rw [hcover]
      exact mem_univ _
    rcases mem_biUnion.mp hf with ⟨i, hi, hf⟩
    exact ⟨i, trivial⟩
  have hm := binary_partial_word_partition_moments s b hconflict hcover
  have horth (a c : Option V) (hac : a ≠ c) :
      (∑ i, w i * y a i * y c i) = 0 := by
    cases a with
    | none =>
      cases c with
      | none => exact (hac rfl).elim
      | some v => simpa [w, y] using hm.1 v
    | some u =>
      cases c with
      | none => simpa [w, y] using hm.1 u
      | some v =>
        exact hm.2 u v (fun he => hac (congrArg some he))
  have hnorm (a : Option V) : (∑ i, w i * y a i * y a i) ≠ 0 := by
    apply ne_of_gt
    cases a with
    | none =>
      obtain ⟨i, hi⟩ := hex
      simpa [y] using (sum_pos' (fun j hj => (hw j).le)
        ⟨i, mem_univ _, hw i⟩)
    | some v =>
      obtain ⟨i, hi⟩ := hessential v
      apply sum_pos'
      · intro j hj
        have hq := sq_nonneg (y (some v) j)
        nlinarith [hw j]
      · refine ⟨i, mem_univ _, ?_⟩
        dsimp [y, binary_partial_word_sign]
        rw [if_pos hi]
        cases hbit : b i v <;> simpa [binary_bool_sign, hbit] using hw i
  simpa only [Fintype.card_option] using weighted_orthogonal_card_bound w y horth hnorm
