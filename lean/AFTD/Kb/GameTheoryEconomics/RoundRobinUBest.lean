import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BordaBundleUtility
import AFTD.Kb.GameTheoryEconomics.RoundRobinSequence
import AFTD.Kb.GameTheoryEconomics.PickingSequenceOutcome

/-!
# round_robin_u_best

Topic: fair_division   Node: e9e484d72f7f

Provenance: formalization of a published result. Source: Algorithms for Manipulating Sequential Allocation (AAAI 2020)

In the alternating Round-Robin picking sequence ABAB...AB of m goods, agent A's best-response Borda utility U_best is the maximum of A's true Borda utility over all m! ranking reports that A can submit, after observing B's true ranking rB.
-/

/-- Maximum Borda utility of agent A over all m! ranking reports against truthful agent B in alternating Round-Robin draft. -/
def round_robin_u_best (m : ℕ) (rA rB : Fin m ≃ Fin m) : ℕ :=
  Finset.univ.sup (fun rA' : Fin m ≃ Fin m =>
    borda_bundle_utility m rA
      (picking_sequence_outcome (round_robin_sequence 2 m) (fun i => if i = 0 then rA' else rB) 0))
