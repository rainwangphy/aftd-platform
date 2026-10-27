import AFTD.Prelude
import AFTD.Kb.Tcs.BinaryPartialWordCube
import AFTD.Kb.Tcs.BinaryPartialWordCubeMem

/-!
# binary_partial_word_cube_cover_iff

Topic: combinatorics   Node: 6c0e3ca4fc52

Provenance: helper lemma. Reusable finite-cube and ordered-biclique helpers for the uniform OP-205 / RT-1 full-root-gap reduction following arXiv:2610.15635. The deficiency-one singular-coordinate/tree argument formalizes the Boolean setting of arXiv:1103.3693 Lemma 2.5.4 and Corollary 2.5.6; arXiv:2212.14685 Section 2.3 gives a related partition-size discussion. These are helper formalizations, not an original graph covering result; no advance is claimed.

A family of partial-word cubes covers the whole Boolean cube exactly when every Boolean assignment agrees with one of the partial words on its support.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem binary_partial_word_cube_cover_iff {I V : Type*} [Fintype I] [Fintype V]
    [DecidableEq V] (s : I → Finset V) (b : I → V → Bool) :
    (univ.biUnion (fun i => binary_partial_word_cube (s i) (b i))) = univ ↔
      ∀ f : V → Bool, ∃ i, ∀ v ∈ s i, f v = b i v := by
  classical
  constructor
  · intro h f
    have hf : f ∈ univ.biUnion (fun i => binary_partial_word_cube (s i) (b i)) := by
      rw [h]
      exact mem_univ _
    rcases mem_biUnion.mp hf with ⟨i, hi, hfi⟩
    exact ⟨i, (binary_partial_word_cube_mem _ _ _).mp hfi⟩
  · intro h
    apply eq_univ_of_forall
    intro f
    obtain ⟨i, hi⟩ := h f
    exact mem_biUnion.mpr ⟨i, mem_univ _, (binary_partial_word_cube_mem _ _ _).mpr hi⟩
