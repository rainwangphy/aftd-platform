import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PyranimStablePositions
import AFTD.Kb.GameTheoryEconomics.PyranimGameIso

/-!
# pyranim_collision_prob

Topic: combinatorial_games   Node: 9f52cb2dc019

Provenance: formalization of a published result. Source: arXiv:2611.16153 Sec. 5.3, Question 4

For a natural number n, pyranim_collision_prob n is the ratio of the number of pairs (X, Y) in pyranim_stable_positions n ×ˢ pyranim_stable_positions n satisfying pyranim_game_iso X Y to the square of the cardinality of pyranim_stable_positions n, as a real number.
-/

/-- The probability that two independent uniformly chosen stable Pyranim positions on n tiers are game-isomorphic. -/
noncomputable def pyranim_collision_prob (n : ℕ) : ℝ := let T := pyranim_stable_positions n
  (@Finset.filter (Finset (ℕ × ℕ) × Finset (ℕ × ℕ)) (fun ⟨X, Y⟩ => pyranim_game_iso X Y) (fun _ => Classical.propDecidable _) (T ×ˢ T)).card / (T.card ^ 2 : ℝ)
