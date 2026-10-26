import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianHeightGraph
import AFTD.Kb.Tcs.MondrianHeightGraphAdjOfMem
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianPartitionIsolatedRowFunction
import AFTD.Kb.Tcs.MondrianRectWidth
import AFTD.Kb.Tcs.MondrianRectCells
import AFTD.Kb.Tcs.MondrianRectCongruent
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# mondrian_partition_width_free_height_reachable

Topic: combinatorics   Node: d9f02ff01124

Provenance: helper lemma. Helper for OP-280, arXiv:2610.19193, Section 1. Height-level networks are motivated by the graph model in arXiv:2007.09639, Section 1; the filtered graph and row-potential cut argument are developed here for the remaining cases with at least three prime factors.

If d divides the square side and a tile has width indivisible by d, its bottom and top row levels remain connected in the height graph after removing that tile from the rectangle list.
-/

theorem mondrian_partition_width_free_height_reachable (n d : ℕ) (P : List (ℕ × ℕ × ℕ × ℕ))
    (hP : mondrian_is_partition n P) (hdn : d ∣ n)
    (r : ℕ × ℕ × ℕ × ℕ) (hr : r ∈ P) (hfree : ¬ d ∣ mondrian_rect_width r) :
    (mondrian_height_graph d (P.filter (fun s => decide (s ≠ r)))).Reachable r.2.2.1 r.2.2.2 := by
  classical
  let H := mondrian_height_graph d (P.filter (fun s => decide (s ≠ r)))
  by_contra hnot
  let f : ℕ → ℤ := fun y => if H.Reachable r.2.2.1 y then 0 else 1
  have hstep : f r.2.2.2 - f r.2.2.1 = 1 := by
    simp [f, show ¬ H.Reachable r.2.2.1 r.2.2.2 from hnot]
  have hothers : ∀ s ∈ P, s ≠ r → d ∣ mondrian_rect_width s ∨ f s.2.2.2 = f s.2.2.1 := by
    intro s hs hne
    by_cases hsd : d ∣ mondrian_rect_width s
    · exact Or.inl hsd
    have hadj : H.Adj s.2.2.1 s.2.2.2 := mondrian_height_graph_adj_of_mem d _ s
      (by simp [hs, hne]) hsd (hP.2.1 s hs).2
    have hreach := hadj.reachable
    have heq : H.Reachable r.2.2.1 s.2.2.2 ↔ H.Reachable r.2.2.1 s.2.2.1 :=
      ⟨fun h => h.trans hreach.symm, fun h => h.trans hreach⟩
    exact Or.inr (by simp only [f, heq])
  exact hfree (mondrian_partition_isolated_row_function n d P hP hdn r hr f hstep hothers)
