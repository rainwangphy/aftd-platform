import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsEf1Chores
import AFTD.Kb.GameTheoryEconomics.SocialCost

/-!
# opt_ef1_social_cost

Topic: fair_division   Node: 2d03765b88d0

The minimum social cost over EF1 allocations.
-/

/-- `min_{A ∈ EF1(I)} SC(A)`: the minimum social cost over EF1 allocations (arXiv:2410.15738, Def. 4 with `P` = EF1). -/
noncomputable def opt_ef1_social_cost {m n : ℕ} (c : Fin n → Fin m → ℝ) : ℝ :=
  sInf (social_cost c '' {σ | is_ef1_chores c σ})
