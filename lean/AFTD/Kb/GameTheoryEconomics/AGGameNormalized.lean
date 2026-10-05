import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AGGame

/-!
# AGGame.Normalized

Topic: equilibria   Node: acd457cfc91c

Payoffs lie in [0, 1] (the normalisation of arXiv 0710.5582) on all partitions of the other n − 1 players.
-/

open Finset in
/-- Payoffs lie in `[0, 1]` (the normalisation of arXiv 0710.5582) on all partitions of the other `n − 1` players. -/
def AGGame.Normalized {n s : ℕ} (G : AGGame n s) : Prop :=
  ∀ p i (y : Fin s → ℕ), ∑ j, y j = n - 1 → 0 ≤ G.u p i y ∧ G.u p i y ≤ 1
