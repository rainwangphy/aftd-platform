import AFTD.Prelude

/-!
# perm_cycle_gcd

Topic: elementary_number_theory   Node: ae6a923274b6

Provenance: formalization of a published result. Source: arXiv:2610.40342 Section 6

The greatest common divisor of the cycle lengths of a permutation $\sigma$ on a finite type $\alpha$, where fixed points are counted as cycles of length 1.
-/

/-- The greatest common divisor of all cycle lengths of a permutation, including fixed points. -/
def perm_cycle_gcd {α : Type*} [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) : ℕ := Multiset.gcd (σ.cycleType + Multiset.replicate (Fintype.card α - σ.support.card) 1)
