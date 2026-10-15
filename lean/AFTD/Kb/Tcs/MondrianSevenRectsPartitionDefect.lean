import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianSevenRectsIsPartition
import AFTD.Kb.Tcs.MondrianSevenRectsDefect
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianDefect
import AFTD.Kb.Tcs.MondrianSevenRects

/-!
# mondrian_seven_rects_partition_defect

Topic: combinatorics   Node: 66b809ac466e

Provenance: formalization of a published result. Source: arXiv:2610.19193 (A Bounded-Defect Construction for the Mondrian Art Problem), Proposition 1 (with the partition property stated before it).

Let p, q be positive integers of the same parity with q < p < 7q, n = 105q and E = p² − 19q². The seven rectangles R₁, …, R₇ of (2)–(3) have positive integer sides, partition the n×n square and are pairwise noncongruent, and the defect of this partition is 140|E|.
-/

theorem mondrian_seven_rects_partition_defect (p q : ℕ) (hpar : p % 2 = q % 2) (hqp : q < p)
    (hp : p < 7 * q) :
    mondrian_is_partition (105 * q) (mondrian_seven_rects p q) ∧
      (mondrian_defect (mondrian_seven_rects p q) : ℤ) = 140 * |(p : ℤ) ^ 2 - 19 * (q : ℤ) ^ 2| :=
  ⟨mondrian_seven_rects_is_partition p q hpar hqp hp, mondrian_seven_rects_defect p q hpar hqp hp⟩
