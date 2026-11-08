import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TorusGraph
import AFTD.Kb.GameTheoryEconomics.MovingTargetStrategy
import AFTD.Kb.GameTheoryEconomics.MovingTargetStrategySuccessful
import AFTD.Kb.GameTheoryEconomics.ClosedNeighborhood

/-!
# three_by_cycle_torus_moving_target_accuracy_le_ceil

Topic: combinatorial_games   Node: a4e6b72f8344

Provenance: helper lemma. three_by_cycle_torus_moving_target_accuracy_exact

For every integer n ≥ 3, there exists an adaptive search strategy for a moving target on the 3-by-n torus C_3 □ C_n achieving accuracy at most (3 * n + 1) / 2 starting from the candidate set of all vertices.
-/

noncomputable instance (priority := 10000) three_by_cycle_torus_moving_target_accuracy_le_ceil_decidableRel (n : ℕ) :
    DecidableRel (torus_graph 3 n).Adj := Classical.decRel _

/-- For every n ≥ 3, moving-target search on C_3 □ C_n achieves accuracy at most ceil(3n/2). -/
theorem three_by_cycle_torus_moving_target_accuracy_le_ceil (n : ℕ) (hn : 3 ≤ n) :
    ∃ S : MovingTargetStrategy (Fin 3 × Fin n),
      moving_target_strategy_successful (torus_graph 3 n) ((3 * n + 1) / 2) S Finset.univ := by
  classical
  have hcard_univ : (Finset.univ : Finset (Fin 3 × Fin n)).card = 3 * n := by
    simp
  have hs_le : ((3 * n + 1) / 2) ≤ (Finset.univ : Finset (Fin 3 × Fin n)).card := by
    rw [hcard_univ]
    omega
  obtain ⟨Q, hQsub, hQcard⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin 3 × Fin n)))
      (n := (3 * n + 1) / 2) hs_le
  refine ⟨MovingTargetStrategy.query Q MovingTargetStrategy.stop MovingTargetStrategy.stop, ?_⟩
  simp only [moving_target_strategy_successful]
  simp only [closed_neighborhood]
  simp
  constructor
  · intro _
    have hdiff := Finset.card_sdiff_add_card_eq_card
      (s := Q) (t := (Finset.univ : Finset (Fin 3 × Fin n))) hQsub
    omega
  · intro _
    rw [hQcard]
