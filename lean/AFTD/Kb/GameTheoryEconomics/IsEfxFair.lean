import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# is_efx_fair

Topic: fair_division   Node: cc276a9ff72a

An allocation is EFX-fair to agent i (Garg-Sharma Def. 3, equal entitlements) if, against every other agent j, either i does not envy j, or removing any subset of j's bundle with positive marginal value over i's bundle ends the envy and removing any subset of i's bundle with negative marginal value ends it too.
-/

/-- EFX (Garg-Sharma, arXiv:2502.02815, Def. 3, equal entitlements), judged by agent `i`'s valuation `v i`: against every other agent `j`, either `i` does not envy `j`, or removing any subset `S` of `j`'s bundle with positive marginal value over `i`'s bundle ends the envy, and removing any subset `S` of `i`'s own bundle with negative marginal value ends it too. -/
def is_efx_fair {m n : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (σ : Fin m → Fin n) (i : Fin n) : Prop :=
  ∀ j, j ≠ i → v i (bundle_of σ j) ≤ v i (bundle_of σ i) ∨
    ((∀ S, S ⊆ bundle_of σ j → v i (bundle_of σ i) < v i (bundle_of σ i ∪ S) →
        v i (bundle_of σ j \ S) ≤ v i (bundle_of σ i)) ∧
     (∀ S, S ⊆ bundle_of σ i → v i (bundle_of σ i) < v i (bundle_of σ i \ S) →
        v i (bundle_of σ j) ≤ v i (bundle_of σ i \ S)))
