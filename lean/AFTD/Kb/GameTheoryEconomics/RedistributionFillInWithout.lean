import AFTD.Prelude

/-!
# redistribution_fill_in_without

Topic: mechanism_design   Node: e3eeeaa11c78

Provenance: formalization of a published result. Source: arXiv:2610.10995 (Asymptotically optimal public project redistribution without bounded precision), Sec. 4.3, (25).

The fill-in operation on the reports other than agent i: (A_{-i} f)(t) = (1/(n−1)) Σ_{j≠i} f(t + θ_j).
-/

/-- The fill-in operation on the reports other than `i`:
`(A_{-i} f)(t) = (1/(n-1)) ∑_{j ≠ i} f(t + θ_j)`. -/
noncomputable def redistribution_fill_in_without {n : ℕ} (θ : Fin n → ℝ) (i : Fin n)
    (f : ℝ → ℝ) : ℝ → ℝ :=
  fun t => (1 / ((n : ℝ) - 1)) * ∑ j ∈ Finset.univ.erase i, f (t + θ j)
