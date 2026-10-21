import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RunBoundary

/-!
# run_val

Topic: combinatorial_games   Node: b8f0a67911d9

Provenance: helper lemma. step towards run_grundy_values

The closed-form evaluation of the Grundy value for a run of length k with boundaries α and β: k mod 2 for free-free and blocked_in-blocked_in (and symmetric blocked_out-blocked_out), k for runs with one free end, and for blocked_in-blocked_out (and blocked_out-blocked_in) 1 if k ≥ 2 is even and 0 otherwise.
-/

/-- The expected Grundy value for a run of length k with boundary conditions α and β across all nine combinations in the Game of Arrows. -/
def run_val (k : ℕ) (α β : RunBoundary) : ℕ :=
  match α, β with
  | .free, .free => k % 2
  | .free, .blocked_in => k
  | .free, .blocked_out => k
  | .blocked_in, .free => k
  | .blocked_out, .free => k
  | .blocked_in, .blocked_in => k % 2
  | .blocked_out, .blocked_out => k % 2
  | .blocked_in, .blocked_out => if k ≥ 2 ∧ Even k then 1 else 0
  | .blocked_out, .blocked_in => if k ≥ 2 ∧ Even k then 1 else 0
