import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCyclePower

/-!
# simple_graph_cycle_power_six_one_sanity

Topic: combinatorics   Node: 6ad97c356ef0

Provenance: helper lemma. Sanity lemma for the cycle power, arXiv:2610.15635 (Covering powers of cycles with equivalence subgraphs).

Sanity check: in C_6 (the first power of the 6-cycle), vertices 0 and 5 are adjacent (they wrap around) and 0 and 2 are not.
-/

theorem simple_graph_cycle_power_six_one_sanity :
    (simple_graph_cycle_power 6 1).Adj 0 5 ∧ ¬ (simple_graph_cycle_power 6 1).Adj 0 2 := by
  show ((0 : ZMod 6) ≠ 5 ∧ _) ∧ ¬ ((0 : ZMod 6) ≠ 2 ∧ _)
  decide
