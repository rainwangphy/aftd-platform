import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PickingSequenceOutcome
import AFTD.Kb.GameTheoryEconomics.RoundRobinSequence

/-!
# picking_sequence_outcome_round_robin_two_agents_four_items

Topic: fair_division   Node: 432b0ceb4706

Provenance: formalization of a published result. Source: Sanity lemma for picking_sequence_outcome: Example 3.8 of arXiv:2610.23040.

Example 3.8 of arXiv:2610.23040: with two agents reporting a > b > c > d and b > c > d > a, Round-Robin gives {a, c} to agent 1 and {b, d} to agent 2.
-/

theorem picking_sequence_outcome_round_robin_two_agents_four_items :
    picking_sequence_outcome (round_robin_sequence 2 4)
      (fun i : Fin 2 => if i = 0 then Equiv.refl (Fin 4)
        else ⟨![1, 2, 3, 0], ![3, 0, 1, 2], by decide, by decide⟩) = ![{0, 2}, {1, 3}] := by first | (simp_all; done) | omega | decide | linarith | positivity | (aesop; done)
