import AFTD.Prelude
import AFTD.Kb.Optimization.SevenArc

/-!
# seven_cost

Topic: submodular   Node: 6d6cbecc838f

Provenance: formalization of a published result. Source: arXiv:2611.23244 Equation (3)

The total routing cost on the seven-vertex network, given by the sum of unit arc costs times arc loads across all nine arcs.
-/

/-- Total routing cost on the seven-vertex network under arc loads and unit arc costs. -/
def seven_cost (load : SevenArc → ℝ) (l : SevenArc → ℝ) : ℝ := l SevenArc.su * load SevenArc.su + l SevenArc.uv * load SevenArc.uv + l SevenArc.vw * load SevenArc.vw +
  l SevenArc.vt1 * load SevenArc.vt1 + l SevenArc.wt2 * load SevenArc.wt2 + l SevenArc.wt3 * load SevenArc.wt3 +
  l SevenArc.st1 * load SevenArc.st1 + l SevenArc.st2 * load SevenArc.st2 + l SevenArc.ut3 * load SevenArc.ut3
