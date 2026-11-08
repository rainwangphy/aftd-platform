import AFTD.Prelude

/-!
# descent_drift_field

Topic: equilibria   Node: e3de17b24f6f

Provenance: formalization of a published result. Source: arXiv:2611.06076:808

The continuous-time descent drift vector field at memory weight H and scaled satisfaction ς with descent rate η and threshold G₀ is (-η * H, η * (ς - G₀)).
-/

/-- Continuous-time descent drift vector field for memory weight H and satisfaction ς. -/
def descent_drift_field (η G₀ : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (-η * p.1, η * (p.2 - G₀))
