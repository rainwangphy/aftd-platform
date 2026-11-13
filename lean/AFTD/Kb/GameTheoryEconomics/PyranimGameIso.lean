import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PyranimOptions

/-!
# pyranim_game_iso

Topic: combinatorial_games   Node: fe06cc457c55

Provenance: formalization of a published result. Source: arXiv:2611.16153 Def. 1.3

Two Pyranim positions X and Y are game-isomorphic if there exists a bisimulation relation R relating X and Y such that whenever R A B holds, there is a bijection between the option sets pyranim_options A and pyranim_options B relating corresponding successor positions under R.
-/

/-- Game isomorphism between two Pyranim positions, defined as bisimulation on option sets. -/
def pyranim_game_iso (X Y : Finset (ℕ × ℕ)) : Prop := ∃ R : Finset (ℕ × ℕ) → Finset (ℕ × ℕ) → Prop,
    R X Y ∧
    ∀ A B, R A B →
      ∃ f : pyranim_options A ≃ pyranim_options B,
        ∀ o : pyranim_options A, R (o : Finset (ℕ × ℕ)) (f o : Finset (ℕ × ℕ))
