import AFTD.Prelude

/-!
# rec_seq_r

Topic: combinatorics   Node: 589bad69d496

Provenance: formalization of a published result. Source: arXiv:2611.17360 line 118

For each natural number k, rec_seq_r k is the natural number defined by Nat.floor (Real.sqrt (2 * (k : ℝ)) + 1 / 2), the natural floor of the real number sqrt(2k) + 1/2.
-/

/-- The recurrence step r(k) as a natural number: Nat.floor(Real.sqrt(2k) + 1/2). -/
noncomputable def rec_seq_r (k : ℕ) : ℕ := Nat.floor (Real.sqrt (2 * (k : ℝ)) + 1 / 2)
