import AFTD.Prelude

/-!
# descent_threshold

Topic: equilibria   Node: 125dbe56f7b4

Provenance: formalization of a published result. Source: arXiv:2611.06076:916

The continuous-time descent satisfaction threshold S_f(H) for activation budget f and memory weight H is (1 + H)² / (f + H).
-/

/-- Continuous-time descent satisfaction threshold S_f(H). -/
noncomputable def descent_threshold (f H : ℝ) : ℝ :=
  (1 + H)^2 / (f + H)
