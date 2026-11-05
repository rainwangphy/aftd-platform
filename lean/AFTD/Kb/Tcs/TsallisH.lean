import AFTD.Prelude

/-!
# tsallis_h

Topic: information   Node: 18bf2457aa44

Provenance: formalization of a published result. Source: arXiv:2611.00868, Eq. (2)

The symmetric binary power function h_alpha(t) is defined as (((1 + t) / 2)^alpha + ((1 - t) / 2)^alpha) / 2.
-/

/-- Binary power entropy kernel h_alpha(t) = (((1+t)/2)^alpha + ((1-t)/2)^alpha) / 2. -/
noncomputable def tsallis_h (α t : ℝ) : ℝ := (((1 + t) / 2) ^ α + ((1 - t) / 2) ^ α) / 2
