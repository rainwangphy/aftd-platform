import AFTD.Prelude

/-!
# mutual_f_information

Topic: information   Node: b18aca57ee6a

Provenance: formalization of a published result. Source: arXiv:2610.21231 (On the subadditivity of mutual f-information), Sec. I (definition of the mutual f-information Ĩ_f).

For a joint probability mass function p_{XY} on finite sets, the mutual f-information is Ĩ_f(X; Y) = D_f(p_{XY} ‖ p_X p_Y) = Σ_{x,y} p_X(x) p_Y(y) f(p_{XY}(x, y) / (p_X(x) p_Y(y))), where p_X, p_Y are the marginals (terms with p_X(x) p_Y(y) = 0 vanish).
-/

/-- Mutual `f`-information `D_f(p_{XY} ‖ p_X ⊗ p_Y)` of a joint mass function `p : X → Y → ℝ` (terms with a zero marginal vanish). -/
noncomputable def mutual_f_information {X Y : Type*} [Fintype X] [Fintype Y] (f : ℝ → ℝ)
    (p : X → Y → ℝ) : ℝ :=
  ∑ x, ∑ y, (∑ y', p x y') * (∑ x', p x' y) *
    f (p x y / ((∑ y', p x y') * (∑ x', p x' y)))
