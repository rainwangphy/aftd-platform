import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Poc8Adj

/-!
# poc8_step

Topic: fair_division   Node: 2c678344ee3e

One breadth-first-search step inside S: add to R every vertex of S adjacent to a vertex of R.
-/

/-- One BFS step: `R` plus all vertices of `S` adjacent to `R`. -/
def poc8_step (S R : Fin 8 → Bool) : Fin 8 → Bool :=
  fun v => R v || (S v && (List.finRange 8).any fun w => R w && poc8_adj w v)
