import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PairwiseMaximinShare
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# is_pmms_fair

Topic: fair_division   Node: 45e25ee54e76

An allocation is pairwise-MMS-fair to agent i if, for every other agent j, i's bundle is worth to i at least i's two-agent maximin share of the union of the two bundles.
-/

/-- Pairwise MMS for agent `i` (Garg-Sharma Def. 11 with F = MMS, equal entitlements): against every other agent `j`, agent `i`'s bundle is worth at least her maximin share of the two bundles `A_i ∪ A_j` split two ways. -/
def is_pmms_fair {m n : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (σ : Fin m → Fin n)
    (i : Fin n) : Prop :=
  ∀ j, j ≠ i → pairwise_maximin_share (v i) (bundle_of σ i ∪ bundle_of σ j) ≤ v i (bundle_of σ i)
