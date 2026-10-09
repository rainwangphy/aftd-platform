import AFTD.Prelude

/-!
# redistribution_fill_in

Topic: mechanism_design   Node: d7b5d69868c1

Provenance: formalization of a published result. Source: arXiv:2610.10995 (Asymptotically optimal public project redistribution without bounded precision), Sec. 4 (fill-in operation A).

The fill-in operation on the reports θ_1..θ_n: (A f)(t) = (1/n) Σ_j f(t + θ_j).
-/

/-- The fill-in operation on reports `θ`: `(A f)(t) = (1/n) ∑_j f(t + θ_j)`. -/
noncomputable def redistribution_fill_in {n : ℕ} (θ : Fin n → ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun t => (1 / (n : ℝ)) * ∑ j, f (t + θ j)
