import AFTD.Prelude

/-!
# chore_opposite_pair

Topic: fair_division   Node: 5012721c7184

Provenance: formalization of a published result. Source: arXiv:2611.04884, Section 4, line 729

Given implicit natural numbers m and n, a hypothesis h2n : 2 * n ≤ m, and an element j : Fin n, chore_opposite_pair is defined as the Finset (Fin m) containing the two elements j.val and 2 * n - 1 - j.val (viewed as elements of Fin m).
-/

/-- The j-th opposite pair Q_j combining chore j with chore 2n - 1 - j in Finset (Fin m). -/
def chore_opposite_pair {m n : ℕ} (h2n : 2 * n ≤ m) (j : Fin n) : Finset (Fin m) :=
  have hj : j.val < m := by
    have := j.isLt
    omega
  have hopp : 2 * n - 1 - j.val < m := by
    have := j.isLt
    omega
  {⟨j.val, hj⟩, ⟨2 * n - 1 - j.val, hopp⟩}
