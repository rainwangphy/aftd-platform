import AFTD.Prelude
import AFTD.Kb.Tcs.Op869BoundedGameSequentialCompose

/-!
# op869_goal_game_strategy_simulation

Topic: online_algorithms   Node: cea3bcad87d4

Provenance: helper lemma. Strategy simulation for the adaptive online-coloring construction in arXiv:2610.41516 Section 2.

A winning finite-game strategy transfers through a relation when legal moves can be simulated, every response can be matched, and related goal states preserve success.
-/

/-- Transfer a finite adaptive strategy through a state relation. -/
theorem op869_goal_game_strategy_simulation {S₁ S₂ M₁ M₂ R₁ R₂ : Type}
    (g₁ : S₁ → Prop) (g₂ : S₂ → Prop) (legal₁ : S₁ → M₁ → Prop)
    (legal₂ : S₂ → M₂ → Prop) (valid₁ : S₁ → M₁ → R₁ → Prop)
    (valid₂ : S₂ → M₂ → R₂ → Prop) (next₁ : S₁ → M₁ → R₁ → S₁)
    (next₂ : S₂ → M₂ → R₂ → S₂) (rel : S₁ → S₂ → Prop)
    (hgoal : ∀ s₁ s₂, rel s₁ s₂ → g₁ s₁ → g₂ s₂)
    (hstep : ∀ s₁ s₂, rel s₁ s₂ → ∀ a₁, legal₁ s₁ a₁ →
      ∃ a₂, legal₂ s₂ a₂ ∧ ∀ r₂, valid₂ s₂ a₂ r₂ →
        ∃ r₁, valid₁ s₁ a₁ r₁ ∧ rel (next₁ s₁ a₁ r₁) (next₂ s₂ a₂ r₂)) :
    ∀ fuel s₁ s₂, rel s₁ s₂ → op869_sequential_goal_game g₁ legal₁ valid₁ next₁ fuel s₁ →
      op869_sequential_goal_game g₂ legal₂ valid₂ next₂ fuel s₂ := by
  intro fuel
  induction fuel with
  | zero =>
      intro s₁ s₂ hrel hgame
      simp [op869_sequential_goal_game] at hgame
  | succ fuel ih =>
      intro s₁ s₂ hrel hgame
      simp only [op869_sequential_goal_game] at hgame ⊢
      obtain ⟨a₁, ha₁, hnext⟩ := hgame
      obtain ⟨a₂, ha₂, hresponses⟩ := hstep s₁ s₂ hrel a₁ ha₁
      refine ⟨a₂, ha₂, ?_⟩
      intro r₂ hr₂
      obtain ⟨r₁, hr₁, hrel'⟩ := hresponses r₂ hr₂
      rcases hnext r₁ hr₁ with hgoal₁ | hgame₁
      · exact Or.inl (hgoal _ _ hrel' hgoal₁)
      · exact Or.inr (ih _ _ hrel' hgame₁)
