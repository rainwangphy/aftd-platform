import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SampfordWeight

/-!
# sampfordTotalWeight

Topic: social_choice   Node: 3fc8f64e54c2

Provenance: helper lemma. step towards sampford_consecutive_house_coupling_loss_delta_four

The total Sampford weight of all size-k subsets of the n parties, i.e. the normalizing constant (the probability of non-rejection) of Sampford's rejective sampling law.
-/

open Classical in
/-- Normalizing constant of Sampford sampling: total weight of all k-subsets. -/
noncomputable def sampfordTotalWeight {n : ℕ} (r : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∑ S ∈ Finset.powersetCard k Finset.univ, sampfordWeight r S
