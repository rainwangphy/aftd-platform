import AFTD.Prelude

/-!
# redistribution_trade

Topic: mechanism_design   Node: 77017120480d

Provenance: formalization of a published result. Source: arXiv:2610.10995 (Asymptotically optimal public project redistribution without bounded precision), Sec. 4 (trade operation T).

The trade operation on the reports: (T f)(t) = (1/n²) Σ_{j,k} f(t − θ_j + θ_k).
-/

/-- The trade operation on reports `θ`: `(T f)(t) = (1/n²) ∑_{j,k} f(t - θ_j + θ_k)`. -/
noncomputable def redistribution_trade {n : ℕ} (θ : Fin n → ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun t => (1 / (n : ℝ) ^ 2) * ∑ j, ∑ k, f (t - θ j + θ k)
