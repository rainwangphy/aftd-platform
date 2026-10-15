import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianDefect

/-!
# mondrian_min_defect_seven

Topic: combinatorics   Node: abdf21eb371f

Provenance: formalization of a published result. Source: arXiv:2610.19193 (A Bounded-Defect Construction for the Mondrian Art Problem), Conjecture 1 (partitions with seven pairwise noncongruent rectangles).

M₇(n): the minimum defect over admissible Mondrian partitions of the n×n square into exactly seven rectangles (⊤ when there is none).
-/

/-- `M₇(n)`, the minimum defect over seven-rectangle Mondrian partitions. -/
noncomputable def mondrian_min_defect_seven (n : ℕ) : ℕ∞ :=
  ⨅ (P : List (ℕ × ℕ × ℕ × ℕ)) (_ : mondrian_is_partition n P ∧ P.length = 7),
    (mondrian_defect P : ℕ∞)
