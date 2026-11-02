import AFTD.Prelude

/-!
# ising_two_layer_quartic_density

Topic: statistical_mechanics   Node: 10690544dde5

Provenance: helper lemma. Auxiliary definition for OP-812, critical two-layer random regular Ising crossover.

The unnormalized quartic density at (x,y) is exp(-a_d (x^4+y^4)+cxy), where a_d=(d-2)(d-1)/(12d^2).
-/

open scoped BigOperators
open MeasureTheory

noncomputable def ising_two_layer_quartic_density (d : ℕ) (c : ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.exp (-(((d : ℝ) - 2) * ((d : ℝ) - 1) / (12 * (d : ℝ)^2)) * (p.1^4 + p.2^4) + c*p.1*p.2)
