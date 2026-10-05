import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Poc8Step

/-!
# poc8_close

Topic: fair_division   Node: f7f4de63a352

k breadth-first-search steps inside S starting from R.
-/

/-- `k` iterated BFS steps inside `S` from `R`. -/
def poc8_close (S R : Fin 8 → Bool) (k : ℕ) : Fin 8 → Bool :=
  match k with
  | 0 => R
  | k + 1 => poc8_step S (poc8_close S R k)
