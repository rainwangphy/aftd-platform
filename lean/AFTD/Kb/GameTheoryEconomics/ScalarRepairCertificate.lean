import AFTD.Prelude

/-!
# scalar_repair_certificate

Topic: equilibria   Node: 4be8a1d6b787

Provenance: formalization of a published result. Source: arXiv:2611.06076:978

The scalar repair progress certificate K_f(H) for activation budget f and memory weight H is (1 + H) * (f + (2f - 1)H) / (f(f + H)).
-/

/-- Scalar repair certificate K_f(H). -/
noncomputable def scalar_repair_certificate (f H : ℝ) : ℝ :=
  (1 + H) * (f + (2 * f - 1) * H) / (f * (f + H))
