import AFTD.Prelude

/-!
# team_tail

Topic: algorithms   Node: c6a8a0021a4c

Poisson-binomial upper tail: team_tail [q₁, …, qₙ] t is the probability that at least t of n independent events with success probabilities q₁, …, qₙ occur (first-step recursion; team_tail_eq_sum below identifies it with the explicit sum over outcome vectors).
-/

/-- Poisson-binomial upper tail: `team_tail [q₁, …, qₙ] t` is the probability that at least `t` of `n` independent events with success probabilities `q₁, …, qₙ` occur (first-step recursion; `team_tail_eq_sum` below identifies it with the explicit sum over outcome vectors). -/
noncomputable def team_tail : List ℝ → ℕ → ℝ := fun
  | [], t => if t = 0 then 1 else 0
  | p :: ps, t => p * team_tail ps (t - 1) + (1 - p) * team_tail ps t
