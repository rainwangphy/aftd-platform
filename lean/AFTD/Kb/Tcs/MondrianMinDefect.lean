import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianDefect

/-!
# mondrian_min_defect

Topic: combinatorics   Node: 34a3637690c7

Provenance: formalization of a published result. Source: arXiv:2610.19193 (A Bounded-Defect Construction for the Mondrian Art Problem), Sec. 1 (M(n)).

M(n): the minimum defect over all admissible Mondrian partitions of the n×n square (⊤ when there is none).
-/

/-- `M(n)`, the minimum Mondrian defect of the `n × n` square (`⊤` if no partition). -/
noncomputable def mondrian_min_defect (n : ℕ) : ℕ∞ :=
  ⨅ (P : List (ℕ × ℕ × ℕ × ℕ)) (_ : mondrian_is_partition n P), (mondrian_defect P : ℕ∞)
