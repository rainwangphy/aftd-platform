import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RoundRobinSequence

/-!
# round_robin_sequence_three_eight

Topic: fair_division   Node: c1136d46a4e1

Provenance: helper lemma. Sanity lemma for round_robin_sequence (the sequence of arXiv:2610.23686 Proposition 1).

The Round-Robin sequence for 3 agents and 8 goods is (1,2,3,1,2,3,1,2).
-/

theorem round_robin_sequence_three_eight : round_robin_sequence 3 8 = [0, 1, 2, 0, 1, 2, 0, 1] := rfl
