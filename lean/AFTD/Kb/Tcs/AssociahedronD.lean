import AFTD.Prelude
import AFTD.Kb.Tcs.AssociahedronQ

/-!
# associahedron_d

Topic: graphs   Node: e4c11fb62ff6

Provenance: formalization of a published result. Source: arXiv:2611.19659, Section 2

The function associahedron_d takes two pairs a and b in (ZMod 2) × (ZMod 2) and returns the sum in ZMod 2 of the second component of a and the first component of b, namely a.2 + b.1.
-/

/-- The preferred child selector D(a, b) = a.2 + b.1 in ZMod 2. -/
def associahedron_d (a b : ZMod 2 × ZMod 2) : ZMod 2 := a.2 + b.1
