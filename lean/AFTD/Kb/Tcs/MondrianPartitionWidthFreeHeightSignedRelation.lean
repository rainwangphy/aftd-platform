import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianHeightGraphWalkSignedHeights
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianPartitionWidthFreeHeightReachable
import AFTD.Kb.Tcs.MondrianRectHeight
import AFTD.Kb.Tcs.MondrianRectWidth
import AFTD.Kb.Tcs.MondrianRectCells
import AFTD.Kb.Tcs.MondrianHeightGraph
import AFTD.Kb.Tcs.MondrianRectCongruent

/-!
# mondrian_partition_width_free_height_signed_relation

Topic: combinatorics   Node: ff4fe9be1684

Provenance: helper lemma. Helper for OP-280, arXiv:2610.19193, Section 1. Height-level networks are motivated by the graph model in arXiv:2007.09639, Section 1; the filtered graph and row-potential cut argument are developed here for the remaining cases with at least three prime factors.

If d divides the square side and a selected tile has width indivisible by d, its height is a signed sum of heights of other, pairwise distinct tiles whose widths are also indivisible by d.
-/

theorem mondrian_partition_width_free_height_signed_relation (n d : ℕ) (P : List (ℕ × ℕ × ℕ × ℕ))
    (hP : mondrian_is_partition n P) (hdn : d ∣ n)
    (r : ℕ × ℕ × ℕ × ℕ) (hr : r ∈ P) (hfree : ¬ d ∣ mondrian_rect_width r) :
    ∃ L : List ((ℕ × ℕ × ℕ × ℕ) × Bool),
      (L.map Prod.fst).Nodup ∧
      (∀ t ∈ L, t.1 ∈ P ∧ t.1 ≠ r ∧ ¬ d ∣ mondrian_rect_width t.1) ∧
      (L.map (fun t => if t.2 then (mondrian_rect_height t.1 : ℤ)
        else -(mondrian_rect_height t.1 : ℤ))).sum = (mondrian_rect_height r : ℤ) := by
  classical
  have hreach := mondrian_partition_width_free_height_reachable n d P hP hdn r hr hfree
  apply hreach.elim_path
  intro path
  obtain ⟨L, hL, hmem, hsum⟩ := mondrian_height_graph_walk_signed_heights d
    (P.filter (fun s => decide (s ≠ r))) (by
      intro s hs
      exact Nat.le_of_lt (hP.2.1 s (List.mem_filter.mp hs).1).2)
    r.2.2.1 r.2.2.2 path.val
  have hnodup : (L.map Prod.fst).Nodup := by
    apply List.Nodup.of_map (fun s : ℕ × ℕ × ℕ × ℕ => Sym2.mk s.2.2.1 s.2.2.2)
    have hh := path.property.isTrail.edges_nodup
    rw [← hL] at hh
    simpa only [List.map_map, Function.comp_def] using hh
  refine ⟨L, hnodup, ?_, ?_⟩
  · intro t ht
    obtain ⟨htP, htfree⟩ := hmem t ht
    obtain ⟨htP, htne⟩ := List.mem_filter.mp htP
    exact ⟨htP, of_decide_eq_true htne, htfree⟩
  · change _ = ((r.2.2.2 - r.2.2.1 : ℕ) : ℤ)
    rw [Int.ofNat_sub (Nat.le_of_lt (hP.2.1 r hr).2)]
    exact hsum
