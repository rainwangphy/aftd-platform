import AFTD.Prelude

/-!
# is_k_diagonal_on

Topic: combinatorics   Node: 29a71e52ea38

Provenance: formalization of a published result. Source: arXiv:2610.26686 Section 3, above Lemma 3

Let V be a finite subset of U. A function f : U^k -> ℚ is k-diagonal on V if for all x : Fin k -> U with all coordinates in V, f(x) ≠ 0 if and only if all entries of x are equal.
-/

/-- A k-ary function f on U is k-diagonal on V if on tuples from V it is non-zero exactly when all entries are equal. -/
def is_k_diagonal_on {U : Type*} {k : ℕ} (V : Finset U) (f : (Fin k → U) → ℚ) : Prop := ∀ x : Fin k → U, (∀ i, x i ∈ V) → (f x ≠ 0 ↔ ∀ i j : Fin k, x i = x j)
