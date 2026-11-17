import AFTD.Prelude
import AFTD.Kb.Tcs.Op869BoundedGameSequentialCompose

/-!
# op869_macro_step_strategy_simulation

Topic: online_algorithms   Node: c37c4725b2b7

Provenance: helper lemma. AFTD formalization of arXiv:2610.41516, Lemma 2.5

A strategy in one finite game transfers to another if each source move can be simulated by at most B target moves, preserving a state relation or reaching the target goal early.
-/

theorem op869_game_early_bind {S M R : Type} (goal intermediate : S → Prop)
    (legal : S → M → Prop) (valid : S → M → R → Prop) (next : S → M → R → S)
    (m n : ℕ) (s : S)
    (hfirst : op869_sequential_goal_game intermediate legal valid next m s)
    (hcont : ∀ s, intermediate s → goal s ∨ op869_sequential_goal_game goal legal valid next n s) :
    op869_sequential_goal_game goal legal valid next (m+n) s := by
  induction m generalizing s with
  | zero => simp [op869_sequential_goal_game] at hfirst
  | succ m ih =>
    simp only [op869_sequential_goal_game] at hfirst
    simp only [Nat.succ_add, op869_sequential_goal_game]
    obtain ⟨a, ha, hnext⟩ := hfirst
    refine ⟨a, ha, ?_⟩
    intro r hr
    rcases hnext r hr with hmid | hrest
    · rcases hcont _ hmid with hgoal | hfuture
      · exact Or.inl hgoal
      · right
        exact op869_sequential_fuel_mono_internal goal legal valid next n (m+n) _ (by omega) hfuture
    · exact Or.inr (ih _ hrest)

/-- A many-move strategy-simulation principle for the online-coloring construction. -/
theorem op869_macro_step_strategy_simulation {S₁ S₂ M₁ M₂ R₁ R₂ : Type}
    (g₁ : S₁ → Prop) (g₂ : S₂ → Prop) (legal₁ : S₁ → M₁ → Prop)
    (legal₂ : S₂ → M₂ → Prop) (valid₁ : S₁ → M₁ → R₁ → Prop)
    (valid₂ : S₂ → M₂ → R₂ → Prop) (next₁ : S₁ → M₁ → R₁ → S₁)
    (next₂ : S₂ → M₂ → R₂ → S₂) (rel : S₁ → S₂ → Prop) (B : ℕ)
    (hgoal : ∀ s₁ s₂, rel s₁ s₂ → g₁ s₁ → g₂ s₂)
    (hstep : ∀ s₁ s₂, rel s₁ s₂ → ∀ a₁, legal₁ s₁ a₁ →
      op869_sequential_goal_game
        (fun s₂' => g₂ s₂' ∨ ∃ r₁, valid₁ s₁ a₁ r₁ ∧ rel (next₁ s₁ a₁ r₁) s₂')
        legal₂ valid₂ next₂ B s₂) :
    ∀ fuel s₁ s₂, rel s₁ s₂ → op869_sequential_goal_game g₁ legal₁ valid₁ next₁ fuel s₁ →
      op869_sequential_goal_game g₂ legal₂ valid₂ next₂ (B*fuel) s₂ := by
  intro fuel
  induction fuel with
  | zero =>
    intro s₁ s₂ hrel hsource
    simp [op869_sequential_goal_game] at hsource
  | succ fuel ih =>
    intro s₁ s₂ hrel hsource
    simp only [op869_sequential_goal_game] at hsource
    obtain ⟨a₁, ha₁, hnext⟩ := hsource
    have hfirst := hstep s₁ s₂ hrel a₁ ha₁
    have hcont : ∀ s₂',
        (g₂ s₂' ∨ ∃ r₁, valid₁ s₁ a₁ r₁ ∧ rel (next₁ s₁ a₁ r₁) s₂') →
        g₂ s₂' ∨ op869_sequential_goal_game g₂ legal₂ valid₂ next₂ (B*fuel) s₂' := by
      intro s₂' h
      rcases h with hgoal₂ | ⟨r₁, hr₁, hrel'⟩
      · exact Or.inl hgoal₂
      · rcases hnext r₁ hr₁ with hgoal₁ | hgame
        · exact Or.inl (hgoal _ _ hrel' hgoal₁)
        · exact Or.inr (ih _ _ hrel' hgame)
    have hout := op869_game_early_bind g₂
      (fun s₂' => g₂ s₂' ∨ ∃ r₁, valid₁ s₁ a₁ r₁ ∧ rel (next₁ s₁ a₁ r₁) s₂')
      legal₂ valid₂ next₂ B (B*fuel) s₂ hfirst hcont
    have heq : B + B*fuel = B*(fuel+1) := by ring
    rwa [heq] at hout
