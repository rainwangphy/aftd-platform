import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianRectCells
import AFTD.Kb.Tcs.MondrianRectCongruent

/-!
# mondrian_is_partition

Topic: combinatorics   Node: 025e7933d9ad

Provenance: formalization of a published result. Source: arXiv:2610.19193 (A Bounded-Defect Construction for the Mondrian Art Problem), Sec. 1 (admissible partitions of the canvas).

An admissible Mondrian partition of the n×n square: at least two axis-parallel rectangles with positive integer side lengths, with pairwise disjoint interiors, pairwise noncongruent (rotations allowed), covering the canvas [0,n]×[0,n].
-/

/-- An admissible Mondrian partition of the `n × n` square. -/
def mondrian_is_partition (n : ℕ) (P : List (ℕ × ℕ × ℕ × ℕ)) : Prop :=
  2 ≤ P.length ∧ (∀ r ∈ P, r.1 < r.2.1 ∧ r.2.2.1 < r.2.2.2) ∧
    P.Pairwise (fun r s => Disjoint (mondrian_rect_cells r) (mondrian_rect_cells s) ∧
      ¬ mondrian_rect_congruent r s) ∧
    P.toFinset.biUnion mondrian_rect_cells = Finset.range n ×ˢ Finset.range n
