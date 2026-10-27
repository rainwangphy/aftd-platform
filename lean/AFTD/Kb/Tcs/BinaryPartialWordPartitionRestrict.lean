import AFTD.Prelude
import AFTD.Kb.Tcs.BinaryPartialWordCube
import AFTD.Kb.Tcs.BinaryPartialWordCubeCoverIff
import AFTD.Kb.Tcs.BinaryPartialWordRestrictSupport

/-!
# binary_partial_word_partition_restrict

Topic: combinatorics   Node: b14a02ab44f9

Provenance: helper lemma. Reusable finite-cube and ordered-biclique helpers for the uniform OP-205 / RT-1 full-root-gap reduction following arXiv:2610.15635. The deficiency-one singular-coordinate/tree argument formalizes the Boolean setting of arXiv:1103.3693 Lemma 2.5.4 and Corollary 2.5.6; arXiv:2212.14685 Section 2.3 gives a related partition-size discussion. These are helper formalizations, not an original graph covering result; no advance is claimed.

Fixing one coordinate of a finite partial-word cube partition and retaining the compatible words gives a partition with the same pairwise-conflict property on the remaining coordinates.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem binary_partial_word_partition_restrict {I V : Type*} [Fintype I] [Fintype V]
    [DecidableEq V] (s : I → Finset V) (b : I → V → Bool)
    (hconflict : ∀ i j, i ≠ j → ∃ v ∈ s i ∩ s j, b i v ≠ b j v)
    (hcover : (univ.biUnion (fun i => binary_partial_word_cube (s i) (b i))) = univ)
    (v : V) (bit : Bool) :
    let J := {i : I // v ∉ s i ∨ b i v = bit}
    let t : J → Finset {w : V // w ≠ v} := fun i =>
      binary_partial_word_restrict_support (s i.val) v
    let c : J → {w : V // w ≠ v} → Bool := fun i w => b i.val w.val
    (∀ i j, i ≠ j → ∃ w ∈ t i ∩ t j, c i w ≠ c j w) ∧
      (univ.biUnion (fun i => binary_partial_word_cube (t i) (c i))) = univ := by
  classical
  dsimp only
  constructor
  · intro i j hij
    obtain ⟨w, hw, hbits⟩ := hconflict i.val j.val (fun h => hij (Subtype.ext h))
    have hwv : w ≠ v := by
      intro h
      subst w
      have hi : b i.val v = bit := i.property.resolve_left
        (by simpa only [not_not] using (mem_inter.mp hw).1)
      have hj : b j.val v = bit := j.property.resolve_left
        (by simpa only [not_not] using (mem_inter.mp hw).2)
      exact hbits (hi.trans hj.symm)
    refine ⟨⟨w, hwv⟩, ?_, hbits⟩
    simpa only [mem_inter, binary_partial_word_restrict_support, mem_filter, mem_univ,
      true_and] using hw
  · rw [binary_partial_word_cube_cover_iff]
    intro f
    let ext : V → Bool := fun w => if h : w = v then bit else f ⟨w, h⟩
    obtain ⟨i, hi⟩ := (binary_partial_word_cube_cover_iff s b).mp hcover ext
    have hisurv : v ∉ s i ∨ b i v = bit := by
      by_cases hv : v ∈ s i
      · right
        simpa only [ext, dif_pos rfl] using (hi v hv).symm
      · exact Or.inl hv
    refine ⟨⟨i, hisurv⟩, ?_⟩
    intro w hw
    have hwi : w.val ∈ s i := (mem_filter.mp hw).2
    have := hi w.val hwi
    simpa only [ext, dif_neg w.property] using this
