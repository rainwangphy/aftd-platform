import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsSteinNumber

/-!
# stein_number_count

Topic: combinatorial_games   Node: 28b0c94a7d12

Provenance: formalization of a published result. Source: arXiv:2611.05898, Definition 1.5

Given a real number X, the counting function stein_number_count X is defined as the real number of natural numbers n in Finset.Ioc 0 ⌊X⌋₊ that satisfy is_stein_number n.
-/

/-- The number of E. P. Stein numbers less than or equal to X. -/
noncomputable def stein_number_count (X : ℝ) : ℝ :=
  open Classical in ((Finset.Ioc 0 ⌊X⌋₊).filter is_stein_number).card
