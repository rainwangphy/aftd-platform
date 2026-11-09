import AFTD.Prelude
import AFTD.Kb.NumberTheory.OddSquarefreeIndicator

/-!
# odd_squarefree_indicator_prime_sq

Topic: elementary_number_theory   Node: 1956368425d9

Provenance: helper lemma. arXiv:2611.05898, An Asymptotic for E. P. Stein Numbers, Definition 2.1

For any prime natural number $p$ with $p \neq 2$, the odd square-free indicator of $p^2$ is equal to $0$.
-/

/-- The odd square-free indicator of the square of an odd prime is 0. -/
theorem odd_squarefree_indicator_prime_sq (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    odd_squarefree_indicator (p ^ 2) = 0 := by
  simp only [odd_squarefree_indicator]
  rw [if_neg]
  intro h
  exact h p hp hp2 dvd_rfl
