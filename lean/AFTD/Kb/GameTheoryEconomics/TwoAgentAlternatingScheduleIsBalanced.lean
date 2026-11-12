import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TwoAgentAlternatingSchedule
import AFTD.Kb.GameTheoryEconomics.IsBalancedSchedule

/-!
# two_agent_alternating_schedule_is_balanced

Topic: fair_division   Node: 19951978a6e6

Provenance: helper lemma. arXiv:2611.09685

For every number of goods m : ℕ, the alternating drafting schedule two_agent_alternating_schedule m of length m is a balanced schedule for two agents.
-/

/-- The canonical two-agent alternating schedule of length m is a balanced schedule. -/
theorem two_agent_alternating_schedule_is_balanced (m : ℕ) :
    is_balanced_schedule 2 m (two_agent_alternating_schedule m) := by
  dsimp [is_balanced_schedule, two_agent_alternating_schedule]
  constructor
  · intro b hb j1 j2 h
    have hval := congr_arg Fin.val h
    dsimp at hval
    ext
    omega
  · intro j1 j2 h
    have hval := congr_arg Fin.val h
    dsimp at hval
    ext
    omega
