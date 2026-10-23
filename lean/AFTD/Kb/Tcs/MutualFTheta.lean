import AFTD.Prelude

/-!
# mutual_f_theta

Topic: information   Node: 9c2ceebd698c

Provenance: formalization of a published result. Source: arXiv:2610.21231 (On the subadditivity of mutual f-information), Appendix B, proof of Theorem 1, eq. (14)

The function Θ_{p_X,p_{Y|X}}(r_X) of eq. (14)/(19) of arXiv:2610.21231: Σ_y r_Y(y) D_f(r_{X|y} ‖ p_X) - D_f(r_X ‖ p_X), with r_{YX} = r_X p_{Y|X}.
-/

/-- Θ_{p_X, P_{Y|X}}(r) = Σ_y r_Y(y) D_f(r_{X|y} ‖ p_X) - D_f(r ‖ p_X), where r_{YX} = r_X P_{Y|X}, r_Y its Y-marginal and r_{X|y} the conditional; D_f(q ‖ p) = Σ_x p(x) f(q(x)/p(x)). -/
noncomputable def mutual_f_theta {X Y : Type*} [Fintype X] [Fintype Y] (f : ℝ → ℝ)
    (pX : X → ℝ) (PY : X → Y → ℝ) (r : X → ℝ) : ℝ :=
  ∑ y, (∑ x, r x * PY x y) * ∑ x, pX x * f (r x * PY x y / (∑ x', r x' * PY x' y) / pX x) -
    ∑ x, pX x * f (r x / pX x)
