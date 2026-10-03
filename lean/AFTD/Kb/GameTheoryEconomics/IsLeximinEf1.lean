import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GoodsUtility
import AFTD.Kb.GameTheoryEconomics.IsEf1Goods
import AFTD.Kb.GameTheoryEconomics.LeximinLt

/-!
# is_leximin_ef1

Topic: fair_division   Node: 2f5937da19a0

An allocation is leximin-optimal among EF1 allocations: it is EF1 and no EF1 allocation is strictly leximin-better.
-/

/-- `σ` is a leximin-optimal allocation among the EF1 allocations: it is EF1 and no EF1 allocation is strictly leximin-better. -/
def is_leximin_ef1 {m n : ℕ} (u : Fin n → Fin m → ℝ) (σ : Fin m → Fin n) : Prop :=
  is_ef1_goods u σ ∧ ∀ τ, is_ef1_goods u τ → ¬ leximin_lt (goods_utility u σ) (goods_utility u τ)
