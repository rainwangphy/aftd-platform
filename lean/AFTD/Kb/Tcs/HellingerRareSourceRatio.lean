import AFTD.Prelude

/-!
# hellinger_rare_source_ratio

Topic: information   Node: 88e9f33f3641

Provenance: formalization of a published result. Source: arXiv:2610.21231 (On the Subadditivity of Mutual f-Information)

For a natural number k : ℕ and a real number u : ℝ, F_k(u) is defined as (1 - u^k + (1 - u^(2*k) - (k : ℝ)*(1 - u^2)*u^(2*k - 2))/2) / ((k : ℝ)*(1 - u)).
-/

/-- The rare-source Hellinger ratio function F_k(u) for k conditionally independent binary channels -/
noncomputable def hellinger_rare_source_ratio (k : ℕ) (u : ℝ) : ℝ := (1 - u ^ k + (1 - u ^ (2 * k) - (k : ℝ) * (1 - u ^ 2) * u ^ (2 * k - 2)) / 2) / ((k : ℝ) * (1 - u))
