import AFTD.Prelude

/-!
# inner_product_c

Topic: circuits   Node: 2e5ec3176e05

Provenance: formalization of a published result. Source: arXiv:2611.06451 Fact 2.1

The L2 inner product of two complex-valued functions f and g on the Boolean hypercube {0,1}^n with respect to the uniform measure is 2^(-n) * ∑_x star(f(x)) * g(x).
-/

/-- L2 inner product of two complex-valued functions on the Boolean hypercube under the uniform measure. -/
noncomputable def inner_product_c {n : ℕ} (f g : (Fin n → Bool) → ℂ) : ℂ := (1 / (2 : ℂ) ^ n) * ∑ x : Fin n → Bool, star (f x) * g x
