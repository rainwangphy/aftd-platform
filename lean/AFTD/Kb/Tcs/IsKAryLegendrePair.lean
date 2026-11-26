import AFTD.Prelude

/-!
# is_k_ary_legendre_pair

Topic: combinatorics   Node: 8e1ec44f55e2

Provenance: formalization of a published result. Source: arXiv:2611.31067, Section 1

Two sequences A and B of length ℓ form a k-ary Legendre pair if all their values are k-th roots of unity and PAF(A, s) + PAF(B, s) = -2 for all nonzero lags s.
-/

/-- Two sequences A, B : Fin ℓ → ℂ form a k-ary Legendre pair if both are k-ary and their periodic autocorrelations sum to -2 for all nonzero lags. -/
def is_k_ary_legendre_pair (k : ℕ) {ℓ : ℕ} [NeZero ℓ] (A B : Fin ℓ → ℂ) : Prop := (∀ j : Fin ℓ, ∃ u : rootsOfUnity k ℂ, ((u : ℂˣ) : ℂ) = A j) ∧
   (∀ j : Fin ℓ, ∃ u : rootsOfUnity k ℂ, ((u : ℂˣ) : ℂ) = B j) ∧
   (∀ s : Fin ℓ, s ≠ 0 →
     (∑ j : Fin ℓ, A j * star (A (j + s))) +
     (∑ j : Fin ℓ, B j * star (B (j + s))) = -2)
