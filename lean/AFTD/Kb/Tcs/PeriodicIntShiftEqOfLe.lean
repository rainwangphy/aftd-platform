import AFTD.Prelude

/-!
# periodic_int_shift_eq_of_le

Topic: combinatorics   Node: 5988b449b5f3

Provenance: helper lemma. Uniform helper for the OP-205 / RT-1 campaign, following arXiv:2610.15635 Section 3. These class-model, pruning and colour-rigidity lemmas do not establish the unresolved graph covering value. No research advance is claimed.

A natural-valued function on the integers with a positive finite period that never decreases under a fixed integer shift is invariant under that shift.
-/

open Finset

theorem periodic_int_shift_eq_of_le
    (n : ℕ) (hn : 0 < n) (h : ℤ) (R : ℤ → ℕ)
    (hperiod : Function.Periodic R (n : ℤ))
    (hle : ∀ v, R v ≤ R (v + h)) :
    ∀ v, R (v + h) = R v := by
  intro v
  have hmono : Monotone (fun j : ℕ => R (v + (j : ℤ) * h)) := by
    apply monotone_nat_of_le_succ
    intro j
    simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_assoc] using
      hle (v + (j : ℤ) * h)
  have hu := hmono (show 1 ≤ n by omega)
  simp only [Nat.cast_one, one_mul] at hu
  have hp : R (v + (n : ℤ) * h) = R v := by
    simpa [mul_comm] using hperiod.int_mul h v
  rw [hp] at hu
  exact le_antisymm hu (hle v)
