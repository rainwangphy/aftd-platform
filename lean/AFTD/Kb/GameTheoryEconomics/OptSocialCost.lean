import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialCost

/-!
# opt_social_cost

Topic: fair_division   Node: 379151866b61

The optimal social cost: the minimum social cost over all allocations.
-/

/-- `OPT(I)`: the minimum social cost over all allocations (arXiv:2410.15738, Def. 4). -/
noncomputable def opt_social_cost {m n : ℕ} (c : Fin n → Fin m → ℝ) : ℝ :=
  ⨅ σ : Fin m → Fin n, social_cost c σ
