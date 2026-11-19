import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SampfordRareGroupRatio

/-!
# sampfordRareGroupFrontier

Topic: social_choice   Node: ba295a450f56

Provenance: formalization of a published result. Source: OP-1944

The rare-group coupling obstruction frontier for n parties, defined as the supremum over all valid partition parameters m + r = n with r ≥ 2 and 1 ≤ k < m of the rare-group deficit ratio.
-/

/-- The rare-group sharp coupling obstruction frontier for n parties. -/
noncomputable def sampfordRareGroupFrontier (n : ℕ) : ℝ :=
  sSup { v : ℝ | ∃ (m r k : ℕ), m + r = n ∧ 2 ≤ r ∧ 1 ≤ k ∧ k < m ∧ v = sampfordRareGroupRatio m r k }
