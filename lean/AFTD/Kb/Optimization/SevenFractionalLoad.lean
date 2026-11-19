import AFTD.Prelude
import AFTD.Kb.Optimization.SevenArc

/-!
# seven_fractional_load

Topic: submodular   Node: 245da3d55671

Provenance: formalization of a published result. Source: arXiv:2611.23244 Section 4.2

The load vector induced by a fractional reference flow on the seven-vertex network routing demands d_1, d_2, d_3 with arborescence path flows a, b, c.
-/

/-- Load vector on the seven-vertex network induced by a fractional reference flow. -/
def seven_fractional_load (d1 d2 d3 a b c : ℝ) (arc : SevenArc) : ℝ := match arc with
  | SevenArc.su => a + b + d3
  | SevenArc.uv => a + b + c
  | SevenArc.vw => b + c
  | SevenArc.vt1 => a
  | SevenArc.wt2 => b
  | SevenArc.wt3 => c
  | SevenArc.st1 => d1 - a
  | SevenArc.st2 => d2 - b
  | SevenArc.ut3 => d3 - c
