import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RunBoundary
import AFTD.Kb.GameTheoryEconomics.RunVal
import AFTD.Kb.GameTheoryEconomics.RunMoveLegal

/-!
# run_options_val

Topic: combinatorial_games   Node: 0877b9c5f100

Provenance: helper lemma. step towards run_grundy_values

In the Game of Arrows, the list of nim-sums of values of sub-runs resulting from all legal moves on a run of length k with boundaries α and β, computed under the valuation run_val.
-/

/-- The list of option nim-sums for a run of length k with boundaries α and β, evaluated using the closed-form valuation run_val. -/
def run_options_val (k : ℕ) (α β : RunBoundary) : List ℕ :=
  (List.range k).flatMap fun idx =>
    let j := idx + 1
    [RunBoundary.blocked_in, RunBoundary.blocked_out].filterMap fun δ =>
      if run_move_legal k α β j δ then
        some (run_val (j - 1) α δ ^^^ run_val (k - j) δ β)
      else
        none
