import AFTD.Prelude

/-!
# agTot

Topic: equilibria   Node: 677a9739e7b6

Total number of players on each strategy.
-/

open Finset in
/-- Total number of players on each strategy. -/
def agTot {n s : ℕ} (σ : Fin n → Fin s) (j : Fin s) : ℕ := (Finset.univ.filter (fun q => σ q = j)).card
