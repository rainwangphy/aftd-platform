import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AGGame

/-!
# AGGame.Lipschitz

Topic: equilibria   Node: 11151c158bca

λ-Lipschitz utilities: |u(x) − u(y)| ≤ λ ‖x − y‖₁ for all partitions x, y of the other n − 1 players.
-/

open Finset in
/-- `λ`-Lipschitz utilities: `|u(x) − u(y)| ≤ λ ‖x − y‖₁` for all partitions `x, y` of the other `n − 1` players. -/
def AGGame.Lipschitz {n s : ℕ} (G : AGGame n s) (lam : ℚ) : Prop :=
  ∀ p i (x y : Fin s → ℕ), ∑ j, x j = n - 1 → ∑ j, y j = n - 1 →
    |G.u p i x - G.u p i y| ≤ lam * ∑ j, |(x j : ℚ) - (y j : ℚ)|
