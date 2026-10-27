import AFTD.Prelude
import AFTD.Kb.Tcs.PeriodicIntShiftEqOfLe

/-!
# periodic_count_eq_of_shift_balance_of_lower_bound

Topic: combinatorics   Node: 70c815c0b2b1

Provenance: helper lemma. Uniform helper for the OP-205 / RT-1 campaign, following arXiv:2610.15635 Section 3. These class-model, pruning and colour-rigidity lemmas do not establish the unresolved graph covering value. No research advance is claimed.

For a finite-period count balance C(v)+R(v)=t+R(v+h), a pointwise lower bound C(v)>=t forces C to be identically t.
-/

open Finset

theorem periodic_count_eq_of_shift_balance_of_lower_bound
    (n t : ℕ) (hn : 0 < n) (h : ℤ) (C R : ℤ → ℕ)
    (hperiod : Function.Periodic R (n : ℤ))
    (hbalance : ∀ v, C v + R v = t + R (v + h))
    (hlower : ∀ v, t ≤ C v) : ∀ v, C v = t := by
  have hle : ∀ v, R v ≤ R (v + h) := by
    intro v
    have hb := hbalance v
    have hl := hlower v
    omega
  have heq := periodic_int_shift_eq_of_le n hn h R hperiod hle
  intro v
  have hb := hbalance v
  rw [heq v] at hb
  omega
