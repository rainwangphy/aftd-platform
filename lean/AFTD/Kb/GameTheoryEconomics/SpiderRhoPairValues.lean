import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiderLegEnd
import AFTD.Kb.GameTheoryEconomics.SpiderRho

/-!
# spider_rho_pair_values

Topic: combinatorial_games   Node: b8c3f800c295

Provenance: helper lemma. step towards spider_mex_incoming_one_outward

For every h ≥ 1 and φ ≠ free, the pair of rho values (spider_rho h inward φ, spider_rho h outward φ) is either (0, 1) or (1, 0).
-/

/-- For any leg length h ≥ 1 and non-free spider leg end φ, one of spider_rho h inward φ and spider_rho h outward φ equals 0 and the other equals 1. -/
theorem spider_rho_pair_values (h : ℕ) (hh : 1 ≤ h) (φ : SpiderLegEnd) (hφ : φ ≠ SpiderLegEnd.free) :
    (spider_rho h SpiderLegEnd.inward φ = 0 ∧ spider_rho h SpiderLegEnd.outward φ = 1) ∨
    (spider_rho h SpiderLegEnd.inward φ = 1 ∧ spider_rho h SpiderLegEnd.outward φ = 0) := by
  cases φ with
  | free => contradiction
  | inward =>
    simp [spider_rho]
    rcases Nat.mod_two_eq_zero_or_one h with h0 | h1
    · left
      have : 2 ≤ h := by omega
      simp [h0, this]
    · right
      simp [h1]
  | outward =>
    simp [spider_rho]
    rcases Nat.mod_two_eq_zero_or_one h with h0 | h1
    · right
      have : 2 ≤ h := by omega
      simp [h0, this]
    · left
      simp [h1]
