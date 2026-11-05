import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LineMinMatchingCost

/-!
# line_min_matching_cost_le

Topic: social_choice   Node: 261a84115347

Provenance: helper lemma. sanity lemma for line_min_matching_cost (OP-1158)

OPT is at most the cost of any perfect matching.
-/

theorem line_min_matching_cost_le {n : ℕ} (a b : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    line_min_matching_cost a b ≤ ∑ i, |a i - b (σ i)| :=
  Finset.inf'_le _ (Finset.mem_univ σ)
