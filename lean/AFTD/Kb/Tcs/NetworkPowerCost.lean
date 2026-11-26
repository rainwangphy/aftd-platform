import AFTD.Prelude

/-!
# network_power_cost

Topic: online_algorithms   Node: fc1c5c62484b

Provenance: formalization of a published result. Source: arXiv:2611.30912 Section 1.1 and Section 2

For a finite set of resources E with cost coefficients c : E → ℝ and exponents pe : E → ℝ, the total network power cost of a load vector x : E → ℝ is Phi(x) = ∑ e ∈ E, c e * (x e)^(pe e).
-/

/-- Total network power cost function Phi(x) = sum_e c_e * x_e^(p_e). -/
noncomputable def network_power_cost {E : Type*} [Fintype E] (c : E → ℝ) (pe : E → ℝ) (x : E → ℝ) : ℝ := ∑ e : E, c e * (x e) ^ (pe e)
