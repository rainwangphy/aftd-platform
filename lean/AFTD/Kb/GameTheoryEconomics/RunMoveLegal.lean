import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RunBoundary

/-!
# run_move_legal

Topic: combinatorial_games   Node: 81ae56bce7b9

Provenance: formalization of a published result. Source: scout/2610-15145-nim-heaps-in-the-game-of-cycles-the-parity-conjecture-fails.md:417

In a run of length k with boundary conditions α and β, orienting edge j in direction δ is legal if and only if (j ≠ 1 or α ∈ {free, δ}) and (j ≠ k or β ∈ {free, δ}).
-/

/-- Predicate deciding whether orienting edge j in direction δ is a legal move on a run of length k with boundary conditions α and β. -/
def run_move_legal (k : ℕ) (α β : RunBoundary) (j : ℕ) (δ : RunBoundary) : Bool :=
  (j ≠ 1 || α = .free || α = δ) && (j ≠ k || β = .free || β = δ)
