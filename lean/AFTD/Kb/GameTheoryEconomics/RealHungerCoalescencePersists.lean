import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.HungerIter
import AFTD.Kb.GameTheoryEconomics.HungerStep

/-!
# real_hunger_coalescence_persists

Topic: combinatorial_games   Node: 790eec3100bd

Provenance: helper lemma. scout/2610-08949-primitive-periods-in-greedy-chip-firing-games.md:111

For any positive natural number n, any n-by-n real matrix P, and any vectors h1, h2 : Fin n → ℝ, if the hunger trajectories from h1 and h2 coalesce at step t, then they remain equal at every step t + k for all k : ℕ.
-/

/-- If two hunger trajectories coalesce at step t, they remain identical at all subsequent steps t + k. -/
theorem real_hunger_coalescence_persists {n : ℕ} [NeZero n] (P : Matrix (Fin n) (Fin n) ℝ) (h1 h2 : Fin n → ℝ) (t : ℕ) (h_coal : hunger_iter P t h1 = hunger_iter P t h2) : ∀ k : ℕ, hunger_iter P (t + k) h1 = hunger_iter P (t + k) h2 := by
  intro k
  rw [hunger_iter, hunger_iter, add_comm t k, Function.iterate_add_apply, Function.iterate_add_apply]
  exact congr_arg ((hunger_step P)^[k]) h_coal
