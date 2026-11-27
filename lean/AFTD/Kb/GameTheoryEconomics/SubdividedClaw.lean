import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SubdividedClawRel

/-!
# subdivided_claw

Topic: combinatorial_games   Node: 9491afbaf966

Provenance: formalization of a published result. Source: arXiv:2611.32746 Prop 2.3, arXiv:2609.37796 Sec 3.1

The once-subdivided claw graph on Fin 7 with center 0 and paths 0-1-4, 0-2-5, 0-3-6, defined as SimpleGraph.fromRel of subdivided_claw_rel.
-/

/-- The once-subdivided claw graph on Fin 7 with center 0 and paths 0-1-4, 0-2-5, 0-3-6. -/
def subdivided_claw : SimpleGraph (Fin 7) :=
  SimpleGraph.fromRel subdivided_claw_rel
