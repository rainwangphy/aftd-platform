import AFTD.Prelude
import AFTD.Kb.Tcs.OrderedFactorizationCount
import AFTD.Kb.Tcs.OrderedFactorizationEquivSigma
import AFTD.Kb.Tcs.OrderedFactorizationFinite

/-!
# orderedFactorizationCount_eq_sum_properDivisors

Topic: combinatorics   Node: c89e8223f1f2

Provenance: formalization of a published result. Source: arXiv:2611.18194 (The Möbius function of factorizations with a simple prime factor), Section 3: the recursion H(m) = Σ_{d|m, d<m} H(d) for m > 1

For m > 1, H(m) = Σ_{d | m, d < m} H(d): an ordered factorization of m is its first factor m/d > 1 followed by an ordered factorization of the proper divisor d.
-/

theorem orderedFactorizationCount_eq_sum_properDivisors (m : ℕ) (hm : 1 < m) :
    orderedFactorizationCount m = ∑ d ∈ m.properDivisors, orderedFactorizationCount d := by
  obtain ⟨e⟩ := orderedFactorization_equiv_sigma m hm
  have : ∀ d : m.properDivisors,
      Finite {t : List ℕ // (∀ a ∈ t, 1 < a) ∧ t.prod = d.1} :=
    fun d => orderedFactorization_finite d.1
  rw [orderedFactorizationCount, Nat.card_congr e, Nat.card_sigma,
    ← Finset.sum_coe_sort m.properDivisors]
  rfl
