import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# maximin_share

Topic: fair_division   Node: fa5794d0f4f7

The maximin share of a valuation among n agents: the maximum, over partitions of the items into n bundles, of the value of the worst bundle.
-/

/-- The maximin share of a valuation among `n` agents (Budish; Garg-Sharma Def. 7): the best worst bundle over all partitions of the items into `n` bundles. -/
noncomputable def maximin_share {m : ℕ} (v : Finset (Fin m) → ℝ) (n : ℕ) : ℝ :=
  ⨆ P : Fin m → Fin n, ⨅ k : Fin n, v (bundle_of P k)
