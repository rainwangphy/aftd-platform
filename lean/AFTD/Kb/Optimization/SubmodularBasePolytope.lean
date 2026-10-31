import AFTD.Prelude

/-!
# submodular_base_polytope

Topic: submodular   Node: 835d9b28b46c

Provenance: formalization of a published result. Source: arXiv:2610.35433:220

The base polytope B(f) of a set function f on Finset (Fin m) is the set of vectors z in ℝ^m such that the sum of z over every subset S is at most f(S), and the total sum over all coordinates equals 1.
-/

/-- The base polytope B(f) of a normalized set function consists of vectors whose subset sums are bounded by f and whose grand total is 1. -/
def submodular_base_polytope {m : ℕ} (f : Finset (Fin m) → ℝ) : Set (Fin m → ℝ) := { z | (∀ S : Finset (Fin m), ∑ k ∈ S, z k ≤ f S) ∧ ∑ k : Fin m, z k = 1 }
