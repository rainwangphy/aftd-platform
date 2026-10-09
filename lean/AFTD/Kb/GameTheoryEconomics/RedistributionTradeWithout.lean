import AFTD.Prelude

/-!
# redistribution_trade_without

Topic: mechanism_design   Node: 117970219b9a

Provenance: formalization of a published result. Source: arXiv:2610.10995 (Asymptotically optimal public project redistribution without bounded precision), Sec. 4.3, (25).

The trade operation on the reports other than agent i: (T_{-i} f)(t) = (1/(n−1)²) Σ_{j≠i} Σ_{k≠i} f(t − θ_j + θ_k).
-/

/-- The trade operation on the reports other than `i`:
`(T_{-i} f)(t) = (1/(n-1)²) ∑_{j ≠ i} ∑_{k ≠ i} f(t - θ_j + θ_k)`. -/
noncomputable def redistribution_trade_without {n : ℕ} (θ : Fin n → ℝ) (i : Fin n)
    (f : ℝ → ℝ) : ℝ → ℝ :=
  fun t => (1 / ((n : ℝ) - 1) ^ 2) *
    ∑ j ∈ Finset.univ.erase i, ∑ k ∈ Finset.univ.erase i, f (t - θ j + θ k)
