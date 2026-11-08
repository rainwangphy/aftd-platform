import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.DescentThreshold
import AFTD.Kb.GameTheoryEconomics.ScalarRepairCertificate

/-!
# repair_drift_separable_identity

Topic: equilibria   Node: 0d6e38086828

Provenance: formalization of a published result. Source: arXiv:2611.06076:974

For all real numbers f, H, and ς with f ≠ 0, H ≠ 0, and f + H ≠ 0, the sum of the memory gradient ((descent_threshold f H - ς) / H²) multiplied by the memory repair drift (f - H) and the satisfaction gradient (1 / H) multiplied by the satisfaction repair drift (1 + H - ς) equals (f / H²) * (scalar_repair_certificate f H - ς).
-/

/-- Drift identity for separable potential functions along repair dynamics. -/
theorem repair_drift_separable_identity (f H ς : ℝ) (hf : f ≠ 0) (hH : H ≠ 0) (hfH : f + H ≠ 0) :
    ((descent_threshold f H - ς) / H^2) * (f - H) + (1 / H) * (1 + H - ς) =
    (f / H^2) * (scalar_repair_certificate f H - ς) := by
  unfold descent_threshold scalar_repair_certificate
  field_simp
  ring
