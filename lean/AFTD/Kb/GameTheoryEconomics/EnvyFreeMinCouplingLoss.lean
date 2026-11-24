import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsAdmissibleLottery
import AFTD.Kb.GameTheoryEconomics.IsEnvyFreeCoupling
import AFTD.Kb.GameTheoryEconomics.SampfordCouplingLoss

/-!
# envy_free_min_coupling_loss

Topic: social_choice   Node: 8f01aa7f60fa

Provenance: formalization of a published result. Source: arXiv:2405.03687, Section 4; OP-2290

For vote shares p : Fin n → ℝ and house size H, envy_free_min_coupling_loss p H is the infimum of sampfordCouplingLoss p H prob over all joint distributions prob that couple some admissible lotteries distH at H and distH1 at H + 1 under is_envy_free_coupling p H distH distH1 prob.
-/

open Classical in
/-- The minimum house-monotonicity coupling loss d(p, H) over all joint laws of admissible envy-free lotteries at house sizes H and H + 1. -/
noncomputable def envy_free_min_coupling_loss {n : ℕ} (p : Fin n → ℝ) (H : ℕ) : ℝ :=
  sInf { L | ∃ distH distH1 prob,
    is_admissible_lottery p H distH ∧
    is_admissible_lottery p (H + 1) distH1 ∧
    is_envy_free_coupling p H distH distH1 prob ∧
    L = sampfordCouplingLoss p H prob }
