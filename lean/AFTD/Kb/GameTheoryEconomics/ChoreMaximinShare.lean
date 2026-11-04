import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# chore_maximin_share

Topic: fair_division   Node: 9c7352be1eae

Provenance: formalization of a published result. Source: arXiv:2611.00432, Section 2.1

The maximin share (MMS) of an agent with additive chore costs u among n agents: the infimum over all partitions P : Fin m → Fin n of the supremum over bundles k : Fin n of the total cost of bundle P k to the agent.
-/

/-- The maximin share (MMS) of an agent with additive chore costs among n agents. -/
noncomputable def chore_maximin_share {m : ℕ} (n : ℕ) (u : Fin m → ℝ) : ℝ := ⨅ P : Fin m → Fin n, ⨆ k : Fin n, additive_valuation u (bundle_of P k)
