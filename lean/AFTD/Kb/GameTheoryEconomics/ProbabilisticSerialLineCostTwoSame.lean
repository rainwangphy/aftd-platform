import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialLineCost
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialFractionalAssignmentTwoSame
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialFractionalAssignment

/-!
# probabilistic_serial_line_cost_two_same

Topic: social_choice   Node: cd8ecc74ae0c

Provenance: helper lemma. sanity lemma for probabilistic_serial_line_cost (OP-1158)

Sanity check: two agents at 0, items at 0 and 1, both ranking item 0 first: the probabilistic serial cost is 1.
-/

theorem probabilistic_serial_line_cost_two_same (pref : Fin 2 → Equiv.Perm (Fin 2))
    (h0 : pref 0 0 = 0) (h1 : pref 1 0 = 0) :
    probabilistic_serial_line_cost (fun _ => 0) ![0, 1] pref = 1 := by
  unfold probabilistic_serial_line_cost
  simp [probabilistic_serial_fractional_assignment_two_same pref h0 h1, Fin.sum_univ_two]
