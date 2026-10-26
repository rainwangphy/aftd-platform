import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianHeightGraph
import AFTD.Kb.Tcs.MondrianRectWidth

/-!
# mondrian_height_graph_adj_of_mem

Topic: combinatorics   Node: f85323e686e2

Provenance: helper lemma. Helper for OP-280, arXiv:2610.19193, Section 1. Height-level networks are motivated by the graph model in arXiv:2007.09639, Section 1; the filtered graph and row-potential cut argument are developed here for the remaining cases with at least three prime factors.

Every positive-height member of the rectangle list whose width is indivisible by d gives a height-graph edge between its bottom and top row levels.
-/

theorem mondrian_height_graph_adj_of_mem (d : ℕ) (P : List (ℕ × ℕ × ℕ × ℕ))
    (r : ℕ × ℕ × ℕ × ℕ) (hr : r ∈ P) (hfree : ¬ d ∣ mondrian_rect_width r)
    (hpos : r.2.2.1 < r.2.2.2) :
    (mondrian_height_graph d P).Adj r.2.2.1 r.2.2.2 := by
  exact ⟨Nat.ne_of_lt hpos, r, hr, hfree, Or.inl ⟨rfl, rfl⟩⟩
