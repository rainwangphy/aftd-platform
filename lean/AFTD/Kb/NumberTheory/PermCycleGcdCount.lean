import AFTD.Prelude
import AFTD.Kb.NumberTheory.PermCycleGcd

/-!
# perm_cycle_gcd_count

Topic: elementary_number_theory   Node: f7dd89b86cfc

Provenance: formalization of a published result. Source: arXiv:2610.40342 Section 6

The number of permutations $\sigma$ of `Fin n` whose greatest common divisor of cycle lengths `perm_cycle_gcd \sigma` equals $g$, where fixed points are counted as cycles of length 1.
-/

/-- Number of permutations of Fin n whose cycle gcd (including 1-cycles) equals g. -/
def perm_cycle_gcd_count (n g : ℕ) : ℕ := (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => perm_cycle_gcd σ = g)).card
