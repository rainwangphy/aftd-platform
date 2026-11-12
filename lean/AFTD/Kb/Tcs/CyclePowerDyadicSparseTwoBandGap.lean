import AFTD.Prelude

/-!
# cycle_power_dyadic_sparse_two_band_gap

Topic: combinatorics   Node: f91c95b8ebdd

Provenance: helper lemma. Sparse defective profiles related to arXiv:2610.15635 and research thread RT-1.

For q at least four, a finite set contained in {0, q-1} together with the half-open interval from 4q-floor(q/2) to 4q contains no pair at distance q-2.
-/

theorem cycle_power_dyadic_sparse_two_band_gap
    (q : ℕ) (hq : 4 ≤ q) (S : Finset ℕ)
    (hS : ∀ a ∈ S, a = 0 ∨ a = q-1 ∨
      (4*q-q/2 ≤ a ∧ a < 4*q)) :
    ∀ a ∈ S, ∀ b ∈ S, a < b → b-a ≠ q-2 := by
  intro a ha b hb hab
  rcases hS a ha with ha0 | ha1 | hat <;>
    rcases hS b hb with hb0 | hb1 | hbt <;> omega
