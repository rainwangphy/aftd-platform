import AFTD.Prelude

/-!
# is_wolfe_corral

Topic: submodular   Node: 738d27d2161b

Provenance: formalization of a published result. Source: arXiv:2611.12680 Sec. 2.2; Wolfe 1976

A non-empty finite set S of atoms in ℝ^n is a corral with affine minimizer w if w is an affine combination of S with strictly positive coefficients and the gap ⟨w, p - w⟩ is zero for all p in S.
-/

/-- A corral S with affine minimizer w in Wolfe's minimum-norm-point method. -/
def is_wolfe_corral {n : ℕ} (S : Finset (Fin n → ℝ)) (w : Fin n → ℝ) : Prop :=
  S.Nonempty ∧
  (∀ p ∈ S, ∑ i : Fin n, w i * (p i - w i) = 0) ∧
  ∃ c : (Fin n → ℝ) → ℝ,
    (∑ p ∈ S, c p = 1) ∧
    (∀ p ∈ S, 0 < c p) ∧
    (w = ∑ p ∈ S, c p • p)
