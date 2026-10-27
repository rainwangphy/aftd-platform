import AFTD.Prelude
import AFTD.Kb.Tcs.BinaryPartialWordCube
import AFTD.Kb.Tcs.BinaryPartialWordRestrictSupport
import AFTD.Kb.Tcs.BinaryPartialWordPartitionBothBits

/-!
# binary_partial_word_partition_min_degree_restrict_essential

Topic: combinatorics   Node: c6ee9d2a684c

Provenance: helper lemma. Reusable finite-cube and ordered-biclique helpers for the uniform OP-205 / RT-1 full-root-gap reduction following arXiv:2610.15635. The deficiency-one singular-coordinate/tree argument formalizes the Boolean setting of arXiv:1103.3693 Lemma 2.5.4 and Corollary 2.5.6; arXiv:2212.14685 Section 2.3 gives a related partition-size discussion. These are helper formalizations, not an original graph covering result; no advance is claimed.

Fixing a coordinate with minimum occurrence count in a finite cube partition that mentions every coordinate leaves every other coordinate mentioned.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem binary_partial_word_partition_min_degree_restrict_essential
    {I V : Type*} [Fintype I] [Fintype V] [DecidableEq V]
    (s : I → Finset V) (b : I → V → Bool)
    (hconflict : ∀ i j, i ≠ j → ∃ v ∈ s i ∩ s j, b i v ≠ b j v)
    (hcover : (univ.biUnion (fun i => binary_partial_word_cube (s i) (b i))) = univ)
    (hessential : ∀ v, ∃ i, v ∈ s i) (v : V)
    (hmin : ∀ w, (univ.filter (fun i => v ∈ s i)).card ≤
      (univ.filter (fun i => w ∈ s i)).card) (bit : Bool) :
    ∀ w : {w : V // w ≠ v},
      ∃ i : {i : I // v ∉ s i ∨ b i v = bit},
        w ∈ binary_partial_word_restrict_support (s i.val) v := by
  classical
  intro w
  by_contra hn
  push Not at hn
  have hnot (i : I) (hwi : w.val ∈ s i) : ¬(v ∉ s i ∨ b i v = bit) := by
    intro hs
    apply hn ⟨i, hs⟩
    simp only [binary_partial_word_restrict_support, mem_filter, mem_univ, true_and]
    exact hwi
  have hsub : univ.filter (fun i => w.val ∈ s i) ⊆
      univ.filter (fun i => v ∈ s i) := by
    intro i hi
    have hwi := (mem_filter.mp hi).2
    have hvi : v ∈ s i := by
      by_contra hv
      exact hnot i hwi (Or.inl hv)
    exact mem_filter.mpr ⟨mem_univ _, hvi⟩
  obtain ⟨j, hjv, hjb⟩ := binary_partial_word_partition_both_bits s b hconflict hcover v
    (hessential v) bit
  have hjnot : j ∉ univ.filter (fun i => w.val ∈ s i) := by
    intro hj
    exact hnot j (mem_filter.mp hj).2 (Or.inr hjb)
  have hjmem : j ∈ univ.filter (fun i => v ∈ s i) := mem_filter.mpr ⟨mem_univ _, hjv⟩
  have hss : univ.filter (fun i => w.val ∈ s i) ⊂
      univ.filter (fun i => v ∈ s i) := by
    refine (ssubset_iff_subset_ne).mpr ⟨hsub, ?_⟩
    intro he
    exact hjnot (he.symm ▸ hjmem)
  have hlt := card_lt_card hss
  have hle := hmin w.val
  omega
