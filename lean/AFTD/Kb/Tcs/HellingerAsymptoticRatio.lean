import AFTD.Prelude

/-!
# hellinger_asymptotic_ratio

Topic: information   Node: 8799803a7ac6

Provenance: formalization of a published result. Source: arXiv:2610.21231 (On the Subadditivity of Mutual f-Information)

The limiting ratio function F_infty(a) for a > 0 is defined as (1 - exp(-a) + (1 - (1 + 2*a)*exp(-2*a))/2) / a, representing the continuous scaling limit of the rare-source ratio F_k(1 - a/k) as k tends to infinity.
-/

/-- Limiting ratio function F_infty(a) for many conditionally independent observations -/
noncomputable def hellinger_asymptotic_ratio (a : ℝ) : ℝ := (1 - Real.exp (-a) + (1 - (1 + 2 * a) * Real.exp (-2 * a)) / 2) / a
