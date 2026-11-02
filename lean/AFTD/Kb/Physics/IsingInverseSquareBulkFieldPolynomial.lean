import AFTD.Prelude
import AFTD.Kb.Physics.IsingInverseSquareRingCoefficient

/-!
# ising_inverse_square_bulk_field_polynomial

Topic: statistical_mechanics   Node: d1650be23077

Provenance: helper lemma. arXiv:2610.39815, Sections 2–4; helper for OP-806.

A real polynomial P represents the order-n bulk field coefficient when, at every real field h, the order-n finite-ring coefficients tend to P(tanh(h)^2) as the ring size tends to infinity.
-/

noncomputable def ising_inverse_square_bulk_field_polynomial (n : ℕ) (P : Polynomial ℝ) : Prop := ∀ h : ℝ, Filter.Tendsto (fun L : ℕ => ising_inverse_square_ring_coefficient n L h)
    Filter.atTop (nhds (P.eval ((Real.tanh h)^2)))
