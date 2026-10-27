import AFTD.Prelude
import AFTD.Kb.Tcs.BinaryPartialWordCubeMinimumIncidence
import AFTD.Kb.Tcs.BinaryPartialWordCubeCoverOfVolumeEq
import AFTD.Kb.Tcs.BinaryPartialWordPartitionOrderConvex
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.BinaryPartialWordCube

/-!
# ordered_biclique_minimum_incidence_intervals

Topic: combinatorics   Node: 1ba4e8ccc912

Provenance: helper lemma. Reusable finite-cube and ordered-biclique helpers for the uniform OP-205 / RT-1 full-root-gap reduction following arXiv:2610.15635. The deficiency-one singular-coordinate/tree argument formalizes the Boolean setting of arXiv:1103.3693 Lemma 2.5.4 and Corollary 2.5.6; arXiv:2212.14685 Section 2.3 gives a related partition-size discussion. These are helper formalizations, not an original graph covering result; no advance is claimed.

Let g be positive and take g-1 bicliques indexed by cuts r+1 of the ordered set Fin g, with the first side strictly above r and the second side at most r. Suppose every biclique is nonempty, every ordered pair is covered, and the sum over vertices of their numbers of incident bicliques plus 2^m equals g(m+1). Then each side of each biclique is order-convex.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem ordered_biclique_minimum_incidence_intervals
    (g m : ℕ) (hg : 0 < g)
    (A B : Fin (g-1) → Finset (Fin g))
    (hA : ∀ r i, i ∈ A r → r.val < i.val)
    (hB : ∀ r i, i ∈ B r → i.val ≤ r.val)
    (hne : ∀ r, (A r ∪ B r).Nonempty)
    (hcover : ∀ i j : Fin g, i < j → ∃ r, i ∈ B r ∧ j ∈ A r)
    (hcost : (∑ i : Fin g, (univ.filter
      (fun r : Fin (g-1) => i ∈ A r ∪ B r)).card) + 2^m = g*(m+1)) :
    (∀ r (i j k : Fin g), i ≤ j → j ≤ k → i ∈ A r → k ∈ A r → j ∈ A r) ∧
    (∀ r (i j k : Fin g), i ≤ j → j ≤ k → i ∈ B r → k ∈ B r → j ∈ B r) := by
  classical
  let s : Fin g → Finset (Fin (g-1)) := fun i =>
    univ.filter (fun r => i ∈ A r ∪ B r)
  let b : Fin g → Fin (g-1) → Bool := fun i r => decide (i ∈ A r)
  have hdis (r : Fin (g-1)) (i : Fin g) (hi : i ∈ B r) : i ∉ A r := by
    intro ha
    have := hA r i ha
    have := hB r i hi
    omega
  have hconflict : ∀ i j, i ≠ j → ∃ r ∈ s i ∩ s j, b i r ≠ b j r := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · obtain ⟨r, hir, hjr⟩ := hcover i j hlt
      refine ⟨r, ?_, ?_⟩
      · simp only [s, mem_inter, mem_filter, mem_univ, true_and, mem_union]
        exact ⟨Or.inr hir, Or.inl hjr⟩
      · simp [b, hdis r i hir, hjr]
    · obtain ⟨r, hjr, hir⟩ := hcover j i hgt
      refine ⟨r, ?_, ?_⟩
      · simp only [s, mem_inter, mem_filter, mem_univ, true_and, mem_union]
        exact ⟨Or.inl hir, Or.inr hjr⟩
      · simp [b, hir, hdis r j hjr]
  have heqcost : (∑ i, (s i).card) + 2^m = Fintype.card (Fin g)*(m+1) := by
    simpa only [s, Fintype.card_fin] using hcost
  have hvolume := (binary_partial_word_cube_minimum_incidence s b m hconflict heqcost).1
  have hfull := binary_partial_word_cube_cover_of_volume_eq s b hconflict hvolume
  have hess : ∀ r, ∃ i, r ∈ s i := by
    intro r
    obtain ⟨i, hi⟩ := hne r
    exact ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩⟩
  have hcard : Fintype.card (Fin g) = Fintype.card (Fin (g-1)) + 1 := by
    simp only [Fintype.card_fin]
    omega
  have horder : ∀ r i j, r ∈ s i → r ∈ s j → b i r = false → b j r = true → i < j := by
    intro r i j hi hj hbi hbj
    have hir : i ∈ A r ∪ B r := (mem_filter.mp hi).2
    have hiB : i ∈ B r := (mem_union.mp hir).resolve_left (by simpa [b] using hbi)
    have hjA : j ∈ A r := by simpa [b] using hbj
    have := hA r j hjA
    have := hB r i hiB
    change i.val < j.val
    omega
  have hconvex := binary_partial_word_partition_order_convex (g-1)
    s b hconflict hfull hess (by simp) hcard horder
  constructor
  · intro r i j k hij hjk hi hk
    have his : r ∈ s i := mem_filter.mpr ⟨mem_univ _, mem_union.mpr (Or.inl hi)⟩
    have hks : r ∈ s k := mem_filter.mpr ⟨mem_univ _, mem_union.mpr (Or.inl hk)⟩
    have hjs := hconvex r i j k hij hjk his hks
    have hjr := (mem_filter.mp hjs).2
    rcases mem_union.mp hjr with ha | hb
    · exact ha
    · have := hA r i hi
      have := hB r j hb
      have : i.val ≤ j.val := hij
      omega
  · intro r i j k hij hjk hi hk
    have his : r ∈ s i := mem_filter.mpr ⟨mem_univ _, mem_union.mpr (Or.inr hi)⟩
    have hks : r ∈ s k := mem_filter.mpr ⟨mem_univ _, mem_union.mpr (Or.inr hk)⟩
    have hjs := hconvex r i j k hij hjk his hks
    have hjr := (mem_filter.mp hjs).2
    rcases mem_union.mp hjr with ha | hb
    · have := hA r j ha
      have := hB r k hk
      have : j.val ≤ k.val := hjk
      omega
    · exact hb
