import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.HasOnlineSingleHighAlphaEfx

/-!
# online_single_high_efx_ratio

Topic: fair_division   Node: 92cf8014be06

Provenance: formalization of a published result. Source: arXiv:2610.34625, Sec. 4

For ratio R, the online single-high EFX competitive ratio for three agents is the supremum of all alpha in [0, 1] such that for every number of goods m >= 1, there exists a deterministic online algorithm guaranteeing alpha-EFX on all single-high valuation profiles with ratio R.
-/

/-- The online single-high EFX competitive ratio for three agents at ratio R is the supremum of alpha in [0, 1] guaranteeing alpha-EFX for all m >= 1. -/
noncomputable def online_single_high_efx_ratio (R : ℝ) : ℝ := sSup {α : ℝ | 0 ≤ α ∧ α ≤ 1 ∧ ∀ m : ℕ, 1 ≤ m → has_online_single_high_alpha_efx 3 m R α}
