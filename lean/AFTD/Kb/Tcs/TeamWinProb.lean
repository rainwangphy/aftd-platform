import AFTD.Prelude
import AFTD.Kb.Tcs.TeamTail

/-!
# team_winProb

Topic: algorithms   Node: 255153ffcf6e

Winning probability of a line-up in the Team Order problem of arXiv:2605.21234: team 1 wins if it wins at least ⌊n/2⌋ + 1 of the n independent matches.
-/

/-- Winning probability of a line-up in the Team Order problem of arXiv:2605.21234: team 1 wins if it wins at least `⌊n/2⌋ + 1` of the `n` independent matches. -/
noncomputable def team_winProb {n : ℕ} (P : Fin n → Fin n → ℝ) (π : Equiv.Perm (Fin n)) : ℝ :=
  team_tail (List.ofFn (fun i => P i (π i))) (n / 2 + 1)
