import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphSmallQuasikernelMaxIndependentCoverCounterexample

/-!
# digraph_seven_cover_counterexample_rigidity

Topic: graphs   Node: 3c70163c9f5f

Provenance: helper lemma. Seven-vertex graph from experiment 13993; uniqueness audited in experiments 13995 and 14019.

Every independent four-vertex set in the displayed seven-vertex graph equals {1,2,3,6}, and every independent set whose closed out-neighborhood covers {1,2,3,6} also equals it.
-/

theorem digraph_seven_cover_counterexample_rigidity :
    (∀ J : Finset (Fin 7), in528_independent J → J.card = 4 →
      J = ({1,2,3,6} : Finset (Fin 7))) ∧
    (∀ Q : Finset (Fin 7), in528_independent Q →
      in528_covers Q ({1,2,3,6} : Finset (Fin 7)) →
      Q = ({1,2,3,6} : Finset (Fin 7))) := by
  decide
