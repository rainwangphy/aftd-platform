import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# weighted_chore_maximin_share

Topic: fair_division   Node: 4950009ae011

Provenance: formalization of a published result. Source: https://arxiv.org/html/2510.06581, Section 2.1, weighted maximin share for chores.

For an agent i, take the infimum over all partitions of the chores among the agents of the supremum, over recipients j, of the additive cost of bundle j divided by weight j; multiply this infimum by weight i. Weights are real and division is Lean real division, including at zero. With positive weights this is the standard weighted chore maximin share.
-/

noncomputable def weighted_chore_maximin_share {m n : ℕ} (w : Fin n → ℝ) (u : Fin m → ℝ) (i : Fin n) : ℝ := w i * (⨅ P : Fin m → Fin n, ⨆ j : Fin n, additive_valuation u (bundle_of P j) / w j)
