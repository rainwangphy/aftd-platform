import AFTD.Prelude

/-!
# associahedron_q

Topic: graphs   Node: a98f47e6684f

Provenance: formalization of a published result. Source: arXiv:2611.19659 Section 2

The binary operation Q on (ZMod 2)^2 defined by Q(a, b) = (a_0 + a_1 + b_0, a_1 + b_0 + b_1 + 1).
-/

/-- The binary operation Q on F_2^2 for associahedron vertex labelling. -/
def associahedron_q (a b : ZMod 2 × ZMod 2) : ZMod 2 × ZMod 2 := (a.1 + a.2 + b.1, a.2 + b.1 + b.2 + 1)
