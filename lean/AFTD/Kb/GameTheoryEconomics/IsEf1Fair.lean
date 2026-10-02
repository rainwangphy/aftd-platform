import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# is_ef1_fair

Topic: fair_division   Node: 2c1b6710a2fd

An allocation is EF1-fair to agent i if, against every other agent j, i does not envy j, or removing some item from j's bundle ends the envy, or removing some item from i's own bundle does.
-/

/-- EF1 (Garg-Sharma, arXiv:2502.02815, Def. 2, equal entitlements), judged by agent `i`'s valuation `v i`: against every other agent `j`, either `i` does not envy `j`, or removing some item from `j`'s bundle ends the envy, or removing some item from `i`'s own bundle does. -/
def is_ef1_fair {m n : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (σ : Fin m → Fin n) (i : Fin n) : Prop :=
  ∀ j, j ≠ i → v i (bundle_of σ j) ≤ v i (bundle_of σ i) ∨
    (∃ g ∈ bundle_of σ j, v i ((bundle_of σ j).erase g) ≤ v i (bundle_of σ i)) ∨
    (∃ c ∈ bundle_of σ i, v i (bundle_of σ j) ≤ v i ((bundle_of σ i).erase c))
