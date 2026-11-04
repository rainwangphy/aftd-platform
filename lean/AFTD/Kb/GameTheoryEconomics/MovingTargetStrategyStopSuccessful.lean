import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MovingTargetStrategy
import AFTD.Kb.GameTheoryEconomics.ClosedNeighborhood
import AFTD.Kb.GameTheoryEconomics.MovingTargetStrategySuccessful

/-!
# moving_target_strategy_stop_successful

Topic: combinatorial_games   Node: 15167ed780d2

Provenance: helper lemma. arXiv:2611.01281 Definition 2.1

For any finite type V with decidable equality and simple graph G on V with decidable adjacency, the immediate stopping strategy MovingTargetStrategy.stop is successful with accuracy Fintype.card V starting from Finset.univ: moving_target_strategy_successful G (Fintype.card V) MovingTargetStrategy.stop Finset.univ.
-/

/-- The immediate stopping strategy is successful with accuracy equal to the vertex count. -/
theorem moving_target_strategy_stop_successful {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    moving_target_strategy_successful G (Fintype.card V) MovingTargetStrategy.stop Finset.univ := by
  simp [moving_target_strategy_successful]
