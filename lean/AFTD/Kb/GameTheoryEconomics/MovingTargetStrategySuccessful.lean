import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MovingTargetStrategy
import AFTD.Kb.GameTheoryEconomics.ClosedNeighborhood

/-!
# moving_target_strategy_successful

Topic: combinatorial_games   Node: 5d4915f0c0cd

Provenance: formalization of a published result. Source: arXiv:2611.01281 Definition 2.1

Given a finite type V with decidable equality, a simple graph G on V with decidable adjacency, an accuracy threshold s : ℕ, a strategy strat : MovingTargetStrategy V, and a candidate set D : Finset V, `moving_target_strategy_successful G s strat D` is a proposition defined by recursion on strat: if strat is stop, then D.card ≤ s; if strat is query Q on_false on_true, let C := closed_neighborhood G D in ((C \ Q).Nonempty → moving_target_strategy_successful G s on_false (C \ Q)) ∧ ((C ∩ Q).Nonempty → moving_target_strategy_successful G s on_true (C ∩ Q)).
-/

/-- Whether an adaptive search strategy is successful with accuracy s starting from a candidate set. -/
def moving_target_strategy_successful {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : ℕ) :
    MovingTargetStrategy V → Finset V → Prop
  | .stop, D => D.card ≤ s
  | .query Q on_false on_true, D =>
    let C := closed_neighborhood G D
    ((C \ Q).Nonempty → moving_target_strategy_successful G s on_false (C \ Q)) ∧
    ((C ∩ Q).Nonempty → moving_target_strategy_successful G s on_true (C ∩ Q))
