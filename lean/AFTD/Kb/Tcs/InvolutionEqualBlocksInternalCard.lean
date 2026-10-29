import AFTD.Prelude

/-!
# involution_equal_blocks_internal_card

Topic: graphs   Node: 5772f42368d8

Provenance: helper lemma. IN-338 structural/repair helpers for OP-306, the prescribed-coloring conjecture in arXiv:2610.22142 Sections3.3.2 and6. Exact matching-involution balance and the method obstruction computed in experiment8464. These are certificate/method lemmas, not new wild-number bounds or research advances.

If an involution preserves the union of two disjoint finite blocks of equal cardinality, the number of vertices paired internally in the first block equals the corresponding number in the second block. It suffices that the involution identity hold on their union.
-/

open Finset
set_option maxHeartbeats 2500000

theorem involution_equal_blocks_internal_card
    {V : Type*} [DecidableEq V] (p : V → V) (A B : Finset V)
    (hdis : Disjoint A B) (hcard : A.card = B.card)
    (hstable : ∀ v ∈ A ∪ B, p v ∈ A ∪ B)
    (hinv : ∀ v ∈ A ∪ B, p (p v) = v) :
    (A.filter fun v => p v ∈ A).card = (B.filter fun v => p v ∈ B).card := by
  have hcross : (A.filter fun v => p v ∈ B).card =
      (B.filter fun v => p v ∈ A).card := by
    refine card_nbij' p p ?_ ?_ ?_ ?_
    · intro v hv
      obtain ⟨hvA, hpB⟩ := mem_filter.mp hv
      exact mem_filter.mpr ⟨hpB, by rw [hinv v (mem_union_left B hvA)]; exact hvA⟩
    · intro v hv
      obtain ⟨hvB, hpA⟩ := mem_filter.mp hv
      exact mem_filter.mpr ⟨hpA, by rw [hinv v (mem_union_right A hvB)]; exact hvB⟩
    · intro v hv
      exact hinv v (mem_union_left B (mem_filter.mp hv).1)
    · intro v hv
      exact hinv v (mem_union_right A (mem_filter.mp hv).1)
  have hApart : A.filter (fun v => p v ∉ A) = A.filter (fun v => p v ∈ B) := by
    ext v
    simp only [mem_filter]
    constructor
    · rintro ⟨hvA, hpA⟩
      exact ⟨hvA, (mem_union.mp (hstable v (mem_union_left B hvA))).resolve_left hpA⟩
    · rintro ⟨hvA, hpB⟩
      exact ⟨hvA, fun hpA => disjoint_left.mp hdis hpA hpB⟩
  have hBpart : B.filter (fun v => p v ∉ B) = B.filter (fun v => p v ∈ A) := by
    ext v
    simp only [mem_filter]
    constructor
    · rintro ⟨hvB, hpB⟩
      exact ⟨hvB, (mem_union.mp (hstable v (mem_union_right A hvB))).resolve_right hpB⟩
    · rintro ⟨hvB, hpA⟩
      exact ⟨hvB, fun hpB => disjoint_left.mp hdis hpA hpB⟩
  have hAcount := card_filter_add_card_filter_not (s := A) (fun v => p v ∈ A)
  have hBcount := card_filter_add_card_filter_not (s := B) (fun v => p v ∈ B)
  rw [hApart] at hAcount
  rw [hBpart] at hBcount
  omega
