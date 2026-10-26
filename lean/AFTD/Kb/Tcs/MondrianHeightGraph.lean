import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianRectWidth

/-!
# mondrian_height_graph

Topic: combinatorics   Node: 04cae774acaf

Provenance: helper lemma. Helper for OP-280, arXiv:2610.19193, Section 1. Height-level networks are motivated by the graph model in arXiv:2007.09639, Section 1; the filtered graph and row-potential cut argument are developed here for the remaining cases with at least three prime factors.

The undirected graph on integer row levels whose edges are the bottom and top levels of tiles with width indivisible by d; loops are omitted.
-/

def mondrian_height_graph (d : ℕ) (P : List (ℕ × ℕ × ℕ × ℕ)) : SimpleGraph ℕ where
  Adj x y := x ≠ y ∧ ∃ r ∈ P, ¬ d ∣ mondrian_rect_width r ∧
    ((x = r.2.2.1 ∧ y = r.2.2.2) ∨ (x = r.2.2.2 ∧ y = r.2.2.1))
  symm := ⟨by
    intro x y h
    obtain ⟨hne, r, hr, hd, hxy⟩ := h
    refine ⟨hne.symm, r, hr, hd, ?_⟩
    rcases hxy with hxy | hxy
    · exact Or.inr ⟨hxy.2, hxy.1⟩
    · exact Or.inl ⟨hxy.2, hxy.1⟩⟩
  loopless := ⟨fun x h => h.1 rfl⟩
