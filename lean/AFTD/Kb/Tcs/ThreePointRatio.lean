import AFTD.Prelude

/-!
# three_point_ratio

Topic: information   Node: 7b706217e061

Provenance: formalization of a published result. Source: arXiv:2611.21275, Section III-A

For elements a, b, c in a field F, three_point_ratio a b c is defined as (c - a) / (b - a).
-/

/-- The ratio ρ(a, b, c) = (c - a) / (b - a) associated with three field elements. -/
def three_point_ratio {F : Type*} [Field F] (a b c : F) : F := (c - a) / (b - a)
