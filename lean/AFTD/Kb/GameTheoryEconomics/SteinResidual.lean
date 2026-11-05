import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SteinNumberCount

/-!
# stein_residual

Topic: combinatorial_games   Node: 16f7122c1a25

Provenance: formalization of a published result. Source: arXiv:2611.05898

Given a real number Y, the normalized residual stein_residual Y is defined as stein_number_count (Y ^ 4) / Y - (4 / Real.pi ^ 2) * Real.log Y.
-/

/-- The normalized residual R(Y) for the Stein number counting function. -/
noncomputable def stein_residual (Y : ℝ) : ℝ :=
  stein_number_count (Y ^ 4) / Y - (4 / Real.pi ^ 2) * Real.log Y
