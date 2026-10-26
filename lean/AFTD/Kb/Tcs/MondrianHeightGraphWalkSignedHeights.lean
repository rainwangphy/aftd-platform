import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianHeightGraph
import AFTD.Kb.Tcs.MondrianRectHeight
import AFTD.Kb.Tcs.MondrianRectWidth

/-!
# mondrian_height_graph_walk_signed_heights

Topic: combinatorics   Node: 565c7ee78239

Provenance: helper lemma. Helper for OP-280, arXiv:2610.19193, Section 1. Height-level networks are motivated by the graph model in arXiv:2007.09639, Section 1; the filtered graph and row-potential cut argument are developed here for the remaining cases with at least three prime factors.

Every walk in the height graph of a positive-height rectangle list is represented by a list of width-indivisible tiles with orientation signs; their signed height sum is the difference of the endpoint row levels, and their unordered endpoint pairs are exactly the walk edges.
-/

theorem mondrian_height_graph_walk_signed_heights (d : ℕ) (P : List (ℕ × ℕ × ℕ × ℕ))
    (hpos : ∀ r ∈ P, r.2.2.1 ≤ r.2.2.2) (u v : ℕ)
    (w : (mondrian_height_graph d P).Walk u v) :
    ∃ L : List ((ℕ × ℕ × ℕ × ℕ) × Bool),
      (L.map (fun t => Sym2.mk t.1.2.2.1 t.1.2.2.2)) = w.edges ∧
      (∀ t ∈ L, t.1 ∈ P ∧ ¬ d ∣ mondrian_rect_width t.1) ∧
      (L.map (fun t => if t.2 then (mondrian_rect_height t.1 : ℤ)
        else -(mondrian_rect_height t.1 : ℤ))).sum = (v : ℤ) - (u : ℤ) := by
  induction w with
  | nil => exact ⟨[], by simp, by simp, by simp⟩
  | @cons u v z hadj w ih =>
    obtain ⟨L, hL, hmem, hsum⟩ := ih
    have hdata : u ≠ v ∧ ∃ r ∈ P, ¬ d ∣ mondrian_rect_width r ∧
        ((u = r.2.2.1 ∧ v = r.2.2.2) ∨ (u = r.2.2.2 ∧ v = r.2.2.1)) := hadj
    obtain ⟨_, r, hr, hfree, hxy⟩ := hdata
    have hheight : (mondrian_rect_height r : ℤ) = (r.2.2.2 : ℤ) - (r.2.2.1 : ℤ) := by
      exact_mod_cast Int.ofNat_sub (hpos r hr)
    rcases hxy with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · refine ⟨(r, true) :: L, ?_, ?_, ?_⟩
      · rw [SimpleGraph.Walk.edges_cons]
        simp only [List.map_cons, hL]
        exact congrArg (fun e => e :: w.edges) (by rw [hu, hv])
      · intro t ht
        rcases List.mem_cons.mp ht with ht | ht
        · subst t; exact ⟨hr, hfree⟩
        · exact hmem t ht
      · change (mondrian_rect_height r : ℤ) +
          (L.map (fun t => if t.2 then (mondrian_rect_height t.1 : ℤ) else -(mondrian_rect_height t.1 : ℤ))).sum =
            (z : ℤ) - (u : ℤ)
        rw [hsum, hheight, hu, hv]
        ring
    · refine ⟨(r, false) :: L, ?_, ?_, ?_⟩
      · rw [SimpleGraph.Walk.edges_cons]
        simp only [List.map_cons, hL]
        exact congrArg (fun e => e :: w.edges) (by rw [hu, hv]; exact Sym2.eq_swap)
      · intro t ht
        rcases List.mem_cons.mp ht with ht | ht
        · subst t; exact ⟨hr, hfree⟩
        · exact hmem t ht
      · change -(mondrian_rect_height r : ℤ) +
          (L.map (fun t => if t.2 then (mondrian_rect_height t.1 : ℤ) else -(mondrian_rect_height t.1 : ℤ))).sum =
            (z : ℤ) - (u : ℤ)
        rw [hsum, hheight, hu, hv]
        ring
