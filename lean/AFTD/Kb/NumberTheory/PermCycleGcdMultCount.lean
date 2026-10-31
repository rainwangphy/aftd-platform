import AFTD.Prelude
import AFTD.Kb.NumberTheory.PermCycleGcd

/-!
# perm_cycle_gcd_mult_count

Topic: elementary_number_theory   Node: 2d952240e3e4

Provenance: helper lemma. step towards perm_cycle_gcd_dvd_pred

The number of permutations of `Fin n` whose cycle-length gcd (fixed points counted as 1-cycles) is a multiple of `m`. Equivalently (for `m > 0`), the number of permutations of `{1, ..., n}` all of whose cycle lengths are divisible by `m`; this is the quantity `b_d(n)` of the source paper.
-/

/-- Number of permutations of `Fin n` whose cycle-length gcd is a multiple of `m`. -/
def perm_cycle_gcd_mult_count (n m : ℕ) : ℕ := (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => m ∣ perm_cycle_gcd σ)).card
