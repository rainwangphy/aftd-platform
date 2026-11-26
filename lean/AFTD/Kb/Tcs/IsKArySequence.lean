import AFTD.Prelude

/-!
# is_k_ary_sequence

Topic: combinatorics   Node: 452048f1e944

Provenance: formalization of a published result. Source: arXiv:2611.31067, Section 1

A complex sequence A of length ℓ is k-ary if all its elements take values in the k-th roots of unity in ℂ.
-/

/-- A sequence A : Fin ℓ → ℂ is k-ary if every element is a k-th root of unity in ℂ. -/
def is_k_ary_sequence (k : ℕ) {ℓ : ℕ} (A : Fin ℓ → ℂ) : Prop := ∀ j : Fin ℓ, ∃ u : rootsOfUnity k ℂ, ((u : ℂˣ) : ℂ) = A j
