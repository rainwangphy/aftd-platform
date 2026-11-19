import AFTD.Prelude
import AFTD.Kb.Tcs.IsRealBapatSunderCounterexample

/-!
# has_real_bapat_sunder_counterexample_of_rank

Topic: combinatorics   Node: 646f212ea2be

Provenance: formalization of a published result. Source: arXiv:2611.23269, Section 5

For a natural number r, has_real_bapat_sunder_counterexample_of_rank r holds if there exist a natural number n and a real positive semidefinite matrix A of size (n+1) x (n+1) such that the rank of A is r and A is a counterexample to the Bapat-Sunder eigenvalue conjecture.
-/

/-- Predicate asserting the existence of a real positive semidefinite Bapat-Sunder counterexample of rank r. -/
def has_real_bapat_sunder_counterexample_of_rank (r : ℕ) : Prop := ∃ (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ),
    A.rank = r ∧ is_real_bapat_sunder_counterexample A
