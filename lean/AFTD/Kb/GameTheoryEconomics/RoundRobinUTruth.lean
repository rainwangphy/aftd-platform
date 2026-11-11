import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BordaBundleUtility
import AFTD.Kb.GameTheoryEconomics.RoundRobinSequence
import AFTD.Kb.GameTheoryEconomics.PickingSequenceOutcome

/-!
# round_robin_u_truth

Topic: fair_division   Node: 4f3cca73b514

Provenance: formalization of a published result. Source: Algorithms for Manipulating Sequential Allocation (AAAI 2020)

In the alternating Round-Robin picking sequence ABAB...AB of m goods, agent A's truthful Borda utility U_truth when both agents A and B report their true rankings rA and rB.
-/

/-- Truthful Borda utility of agent A under alternating Round-Robin draft ABAB...AB. -/
def round_robin_u_truth (m : ℕ) (rA rB : Fin m ≃ Fin m) : ℕ :=
  borda_bundle_utility m rA
    (picking_sequence_outcome (round_robin_sequence 2 m) (fun i => if i = 0 then rA else rB) 0)
