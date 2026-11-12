import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialWelfare

/-!
# social_welfare_empty

Topic: fair_division   Node: bb6f0f2452d5

Provenance: helper lemma. arXiv:2611.12740 Section 7

The social welfare of the empty allocation is zero.
-/

/-- The social welfare of the empty allocation is zero. -/
theorem social_welfare_empty {m n : ℕ} (v : Fin m → ℝ) :
    social_welfare (n := n) v (fun _ => ∅) = 0 := by
  simp [social_welfare, additive_valuation]
