import AFTD.Prelude
import AFTD.Kb.Tcs.FactorizationMobiusToTop
import AFTD.Kb.Tcs.IsNatFactorization
import AFTD.Kb.Tcs.IsFactorizationCoarsening

/-!
# factorizationMobiusToTop_singleton

Topic: combinatorics   Node: 939057ccaec0

Provenance: helper lemma. arXiv:2611.18194 (The Möbius function of factorizations with a simple prime factor): sanity lemma for the factorization-poset definitions

The Möbius function of the factorization poset of n is 1 at the top element: μ(n, n) = 1.
-/

theorem factorizationMobiusToTop_singleton (n : ℕ) : factorizationMobiusToTop n {n} = 1 := by
  rw [factorizationMobiusToTop]; simp
