import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd
import AFTD.Kb.GameTheoryEconomics.SpiderRho

/-!
# spider_rho_zero_same

Topic: combinatorial_games   Node: 45e39f0d41d2

Provenance: helper lemma. step towards spider_mex_incoming_one_outward

For any non-free spider leg end φ, spider_rho 0 φ φ = 0.
-/

/-- For any non-free spider leg end φ, spider_rho 0 φ φ equals 0. -/
theorem spider_rho_zero_same (φ : SpiderLegEnd) (hφ : φ ≠ SpiderLegEnd.free) :
    spider_rho 0 φ φ = 0 := by
  cases φ with
  | free => exact absurd rfl hφ
  | inward => simp [spider_rho]
  | outward => simp [spider_rho]
