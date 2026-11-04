import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ChoreMaximinShare
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# is_alpha_mms_chores

Topic: fair_division   Node: 5059a1013c55

Provenance: formalization of a published result. Source: arXiv:2611.00432, Section 2.1

An allocation σ of m chores among n agents is α-MMS for cost functions c if each agent i's total cost for her assigned bundle bundle_of σ i is at most α times her maximin share chore_maximin_share n (c i).
-/

/-- An allocation is α-MMS for chores if each agent's bundle costs at most α times her maximin share. -/
def is_alpha_mms_chores {m n : ℕ} (α : ℝ) (c : Fin n → Fin m → ℝ) (σ : Fin m → Fin n) : Prop := ∀ i : Fin n, additive_valuation (c i) (bundle_of σ i) ≤ α * chore_maximin_share n (c i)
