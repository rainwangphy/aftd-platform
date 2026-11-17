import AFTD.Prelude
import AFTD.Kb.Tcs.Op869MacroStepStrategySimulation
import AFTD.Kb.Tcs.Op869BoundedGameSequentialCompose
import AFTD.Kb.Tcs.Op869BoundedAdversaryForces

/-!
# op869_fold_macro_step_implies_forcing

Topic: online_algorithms   Node: 358e37c1ca7d

Provenance: helper lemma. AFTD formalization of arXiv:2610.41516, Lemma 2.5

A bounded q-fold coloring strategy transfers to a bounded t-fold strategy whenever a related target state can simulate each source move in B target moves and Bn fits the target board.
-/

/-- The bounded coloring-game instance of the many-move strategy transfer. -/
theorem op869_fold_macro_step_implies_forcing (n n' q t K D D' B : ℕ)
    (rel : Op869SequentialState n → Op869SequentialState n' → Prop)
    (hgoal : ∀ s₁ s₂, rel s₁ s₂ → op869_sequential_goal_internal K s₁ →
      op869_sequential_goal_internal K s₂)
    (hstep : ∀ s₁ s₂, rel s₁ s₂ → ∀ a₁, op869_sequential_legal 3 D s₁ a₁ →
      op869_sequential_goal_game
        (fun s₂' => op869_sequential_goal_internal K s₂' ∨
          ∃ r₁, op869_sequential_valid q s₁ a₁ r₁ ∧
            rel (op869_sequential_next s₁ a₁ r₁) s₂')
        (op869_sequential_legal 3 D') (op869_sequential_valid t) op869_sequential_next B s₂)
    (hinit : rel ⟨0, (fun _ => ∅), (fun _ => ∅)⟩ ⟨0, (fun _ => ∅), (fun _ => ∅)⟩)
    (hbudget : B*n ≤ n')
    (hsource : op869_bounded_adversary_forces 3 q K D n 0 (fun _ : Fin n => ∅) (fun _ : Fin n => ∅)) :
    op869_bounded_adversary_forces 3 t K D' n' 0 (fun _ : Fin n' => ∅) (fun _ : Fin n' => ∅) := by
  have hsource' := (op869_bounded_sequential_equiv_internal 3 q K D n 0 _ _).mpr hsource
  have htarget := op869_macro_step_strategy_simulation
    (op869_sequential_goal_internal K) (op869_sequential_goal_internal K)
    (op869_sequential_legal 3 D) (op869_sequential_legal 3 D')
    (op869_sequential_valid q) (op869_sequential_valid t)
    op869_sequential_next op869_sequential_next rel B hgoal hstep n _ _ hinit hsource'
  have htarget' := op869_sequential_fuel_mono_internal (op869_sequential_goal_internal K)
    (op869_sequential_legal 3 D') (op869_sequential_valid t) op869_sequential_next
    (B*n) n' _ hbudget htarget
  exact (op869_bounded_sequential_equiv_internal 3 t K D' n' 0 _ _).mp htarget'
