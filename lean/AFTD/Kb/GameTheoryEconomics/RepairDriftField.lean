import AFTD.Prelude

/-!
# repair_drift_field

Topic: equilibria   Node: d24804fa820d

Provenance: formalization of a published result. Source: arXiv:2611.06076:884

The continuous-time repair drift vector field at memory weight H and scaled satisfaction ς with activation budget f is (f - H, 1 + H - ς).
-/

/-- Continuous-time repair drift vector field for memory weight H and satisfaction ς. -/
def repair_drift_field (f : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (f - p.1, 1 + p.1 - p.2)
