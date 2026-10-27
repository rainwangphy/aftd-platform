import AFTD.Prelude
import AFTD.Kb.Tcs.BinaryPartialWordCube
import AFTD.Kb.Tcs.BinaryPartialWordPartitionDimensionBound
import AFTD.Kb.Tcs.BinaryPartialWordRestrictSupport
import AFTD.Kb.Tcs.BinaryPartialWordPartitionRestrict
import AFTD.Kb.Tcs.BinaryPartialWordPartitionBothBits
import AFTD.Kb.Tcs.BinaryPartialWordPartitionMinDegreeRestrictEssential

/-!
# binary_partial_word_partition_singular_coordinate

Topic: combinatorics   Node: bddde283ead9

Provenance: helper lemma. Reusable finite-cube and ordered-biclique helpers for the uniform OP-205 / RT-1 full-root-gap reduction following arXiv:2610.15635. The deficiency-one singular-coordinate/tree argument formalizes the Boolean setting of arXiv:1103.3693 Lemma 2.5.4 and Corollary 2.5.6; arXiv:2212.14685 Section 2.3 gives a related partition-size discussion. These are helper formalizations, not an original graph covering result; no advance is claimed.

A finite Boolean cube partition mentioning every coordinate and having exactly one more part than coordinates, with a nonempty coordinate type, has a coordinate appearing exactly once with each Boolean value.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem binary_partial_word_partition_singular_coordinate
    {I V : Type*} [Fintype I] [Fintype V] [DecidableEq V] [Nonempty V]
    (s : I → Finset V) (b : I → V → Bool)
    (hconflict : ∀ i j, i ≠ j → ∃ v ∈ s i ∩ s j, b i v ≠ b j v)
    (hcover : (univ.biUnion (fun i => binary_partial_word_cube (s i) (b i))) = univ)
    (hessential : ∀ v, ∃ i, v ∈ s i)
    (hcard : Fintype.card I = Fintype.card V + 1) :
    ∃ v, ∀ bit : Bool,
      (univ.filter (fun i => v ∈ s i ∧ b i v = bit)).card = 1 := by
  classical
  obtain ⟨v, hv, hmin⟩ := exists_min_image (univ : Finset V)
    (fun w => (univ.filter (fun i => w ∈ s i)).card) univ_nonempty
  have hmin' (w : V) : (univ.filter (fun i => v ∈ s i)).card ≤
      (univ.filter (fun i => w ∈ s i)).card := hmin w (mem_univ _)
  refine ⟨v, ?_⟩
  intro bit
  let J := {i : I // v ∉ s i ∨ b i v = !bit}
  let W := {w : V // w ≠ v}
  let t : J → Finset W := fun i => binary_partial_word_restrict_support (s i.val) v
  let c : J → W → Bool := fun i w => b i.val w.val
  have hr := binary_partial_word_partition_restrict s b hconflict hcover v (!bit)
  have hess := binary_partial_word_partition_min_degree_restrict_essential
    s b hconflict hcover hessential v hmin' (!bit)
  have hbound : Fintype.card W + 1 ≤ Fintype.card J :=
    binary_partial_word_partition_dimension_bound t c hr.1 hr.2 hess
  have hW : Fintype.card W = Fintype.card V - 1 := by
    simpa only [W, Fintype.card_subtype_eq] using
      Fintype.card_subtype_compl (fun w : V => w = v)
  have hVpos : 0 < Fintype.card V := Fintype.card_pos
  have hbalance : Fintype.card J +
      (univ.filter (fun i => v ∈ s i ∧ b i v = bit)).card = Fintype.card I := by
    rw [Fintype.card_subtype]
    have he : (univ.filter (fun i : I => ¬(v ∉ s i ∨ b i v = !bit))) =
        univ.filter (fun i => v ∈ s i ∧ b i v = bit) := by
      ext i
      by_cases hv : v ∈ s i
      · cases hb : b i v <;> cases bit <;> simp [hv, hb]
      · simp [hv]
    have hcount := card_filter_add_card_filter_not (s := univ)
      (fun i : I => v ∉ s i ∨ b i v = !bit)
    simpa only [he, card_univ] using hcount
  obtain ⟨i, hi, hbi⟩ := binary_partial_word_partition_both_bits
    s b hconflict hcover v (hessential v) bit
  have hpos : 0 < (univ.filter (fun i => v ∈ s i ∧ b i v = bit)).card := by
    exact card_pos.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, hi, hbi⟩⟩
  omega
