import AFTD.Prelude
import AFTD.Kb.Tcs.BinaryPartialWordCube
import AFTD.Kb.Tcs.BinaryPartialWordCubeCoverIff

/-!
# binary_partial_word_partition_both_bits

Topic: combinatorics   Node: 3198ccff25b5

Provenance: helper lemma. Reusable finite-cube and ordered-biclique helpers for the uniform OP-205 / RT-1 full-root-gap reduction following arXiv:2610.15635. The deficiency-one singular-coordinate/tree argument formalizes the Boolean setting of arXiv:1103.3693 Lemma 2.5.4 and Corollary 2.5.6; arXiv:2212.14685 Section 2.3 gives a related partition-size discussion. These are helper formalizations, not an original graph covering result; no advance is claimed.

Every mentioned coordinate of a finite partial-word cube partition occurs with both Boolean values.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem binary_partial_word_partition_both_bits {I V : Type*} [Fintype I] [Fintype V]
    [DecidableEq V] (s : I → Finset V) (b : I → V → Bool)
    (hconflict : ∀ i j, i ≠ j → ∃ v ∈ s i ∩ s j, b i v ≠ b j v)
    (hcover : (univ.biUnion (fun i => binary_partial_word_cube (s i) (b i))) = univ)
    (v : V) (hessential : ∃ i, v ∈ s i) :
    ∀ bit : Bool, ∃ i, v ∈ s i ∧ b i v = bit := by
  classical
  obtain ⟨i, hi⟩ := hessential
  let f := Function.update (b i) v (!(b i v))
  obtain ⟨j, hj⟩ := (binary_partial_word_cube_cover_iff s b).mp hcover f
  have hflip : (!(b i v)) ≠ b i v := by cases b i v <;> decide
  have hij : i ≠ j := by
    intro heq
    subst j
    have he := hj v hi
    exact hflip (by simpa only [f, Function.update_self] using he)
  have hvj : v ∈ s j := by
    by_contra hn
    obtain ⟨w, hw, hne⟩ := hconflict i j hij
    have hwv : w ≠ v := by rintro rfl; exact hn (mem_inter.mp hw).2
    have he := hj w (mem_inter.mp hw).2
    exact hne (by simpa only [f, Function.update_of_ne hwv] using he)
  have hbj : b j v = !(b i v) := by
    simpa only [f, Function.update_self] using (hj v hvj).symm
  intro bit
  by_cases hbit : b i v = bit
  · exact ⟨i, hi, hbit⟩
  · refine ⟨j, hvj, hbj.trans ?_⟩
    cases hbi : b i v <;> cases bit <;> simp_all
