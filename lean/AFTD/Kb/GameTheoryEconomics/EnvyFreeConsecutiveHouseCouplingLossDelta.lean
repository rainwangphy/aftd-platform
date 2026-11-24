import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EnvyFreeMinCouplingLoss
import AFTD.Kb.GameTheoryEconomics.HasAdmissibleLottery

/-!
# envy_free_consecutive_house_coupling_loss_delta

Topic: social_choice   Node: 9cc816609747

Provenance: formalization of a published result. Source: OP-2290

For n parties, envy_free_consecutive_house_coupling_loss_delta n is the supremum of envy_free_min_coupling_loss p H over all positive vote shares p : Fin n → ℝ summing to 1 and house sizes H ≥ 1 for which admissible lotteries exist at both H and H + 1.
-/

open Classical in
/-- The maximal consecutive-house coupling loss Delta_n across all valid vote shares p and house sizes H >= 1 that admit admissible lotteries separately at H and H + 1. -/
noncomputable def envy_free_consecutive_house_coupling_loss_delta (n : ℕ) : ℝ :=
  sSup { v | ∃ (p : Fin n → ℝ) (H : ℕ),
    (∀ i, 0 < p i) ∧ ∑ i, p i = 1 ∧ 1 ≤ H ∧
    has_admissible_lottery p H ∧ has_admissible_lottery p (H + 1) ∧
    v = envy_free_min_coupling_loss p H }
